use "promises"

// Tokens for voting on commit
primitive YES fun apply(): Bool => true
primitive NO fun apply(): Bool => false
type Response is (YES | NO)

// Token for ordering behaviours
primitive TOKEN

// Token for acking commit/abort
primitive ACK

/* A behaviour is an actor that encapsulates a coutdown and a callback that is
   the body of the behaviours.
   Once the coutdown hits zero, the callback is called
*/

primitive Start
  fun apply(f: {(Manager)}) => f(Manager)

actor Behaviour
  var _countdown: U64
  var _f: {ref ()} iso

  new create(c: U64, f: {ref ()} iso) =>
    _countdown = c
    _f = consume f

  be countdown() =>
    _countdown = _countdown - 1
    if _countdown == 0 then
      _f()
    end

/*
   A transaction manager creates a when which encapsulates a set of cowns to rendezvous with
   and the callback to run which peels of each cown until all states have been acquired and then
   runs the user provided callback

   We know that at the point of running the behaviour and emptying the state, that each cown has
   reserved itself for this behaviour.
*/

primitive _ABORT
  fun apply(m: Manager tag, cowns: Array[CownI tag] val, b: Behaviour) =>
    var acks = Array[Promise[ACK]]
    for cown in cowns.values() do
      let ack = Promise[ACK]
      acks.push(ack)
      cown.abort(b, ack)
    end

    Promises[ACK].join(acks.values()).next[None]({(_: Array[ACK] val) =>
      m._abort(cowns, b)
    })

primitive _COMMIT
  fun apply(m: Manager tag, cowns: Array[CownI tag] val) =>
    var acks = Array[Promise[ACK]]
    for cown in cowns.values() do
      let ack = Promise[ACK]
      acks.push(ack)
      cown.commit(ack)
    end

    Promises[ACK].join(acks.values()).next[None]({(_: Array[ACK] val) =>
      m._commit(cowns)
    })

actor Manager
  let _msgs: Array[(Array[CownI tag] val, Behaviour)]
  var _processing: Array[CownI tag]

  new create() =>
    _msgs = []
    _processing = []

  be send(cowns: Array[CownI tag] val, b: Behaviour) =>
    _msgs.unshift((cowns, b))
    process()

  fun ref _clear(cowns: Array[CownI tag] val) =>
    for cown in cowns.values() do
      try
        _processing.delete(_processing.find(cown)?)?
      end
    end

  // Log the result of a transaction and clear the cowns from processing
  be _abort(cowns: Array[CownI tag] val, b: Behaviour) =>
    _msgs.push((cowns, b))
    _clear(cowns)
    process()

  be _commit(cowns: Array[CownI tag] val) =>
    _clear(cowns)
    process()

  // Attempt to process a message, abort if we overlap with any cown that is already
  // being processed
  fun ref process() =>
    try
      (let cowns, let b) = _msgs.pop()?

      for c in cowns.values() do
        if _processing.contains(c) then
          _msgs.push((cowns, b))
          return
        end
      end

      _processing.append(cowns)

      // Send all involved cowns the behaviour and wait of their outcomes
      let responses = Array[Promise[Response]]
      for cown in cowns.values() do
        let response = Promise[Response]
        cown.enqueue(b, response)
        responses.push(response)
      end
      Promises[Response].join(responses.values()).next[None]({(responses: Array[Response] val)(m: Manager tag=this) =>
        for commit in responses.values() do
          if not commit() then
            _ABORT(m, cowns, b)
            return
          end
        end
        _COMMIT(m, cowns)
      })
    end

  fun tag when[A: Any #send](c1: Cown[A]): _When[A] =>
    _When[A](this, c1)

  class _When[A: Any #send]
    let _manager: Manager
    let _c1: Cown[A]

    new create(manager: Manager tag, c1: Cown[A]) =>
      _manager = manager
      _c1 = c1

    fun run(f: {ref (Manager, A): A^} iso) =>
      // We need to maintain the iso-ness of the function so we abuse an array to pop the function
      // in and out of the array
      let body = Behaviour(1, {ref ()(fcell = recover iso [ consume f ] end) =>
        try
          _c1.empty({ref (a: A)(ffcell = recover iso [ fcell.pop()? ] end) =>
            try
              _c1.fill(ffcell.pop()?(Manager, consume a))
            end
          } iso)
        end
      } iso)

      _manager.send([_c1], body)

    fun n[B: Any iso](c2: Cown[B]): _When2[A, B] =>
      _When2[A, B](_manager, _c1, c2)

  // A when over 2 cowns
  class _When2[A: Any #send, B: Any #send]
    let _manager: Manager
    let _c1: Cown[A]
    let _c2: Cown[B]

    new create(manager: Manager, c1: Cown[A], c2: Cown[B]) =>
      _manager = manager
      _c1 = c1
      _c2 = c2

    fun run(f: {ref (Manager, A, B): (A^, B^)} iso) =>
      let body = Behaviour(2, {ref ()(fcell = recover iso [ consume f ] end) =>
        try
        _c1.empty({ref (a: A)(ffcell = recover iso [ fcell.pop()? ] end, _c2 = _c2) =>
          try
          _c2.empty({ref (b: B)(facell = recover iso [ (ffcell.pop()?, consume a) ] end, _c1 = _c1) =>
            try
              (let f, let a) = facell.pop()?
              (let a', let b') = f(Manager, consume a, consume b)
              _c1.fill(consume a')
              _c2.fill(consume b')
            end
          } iso)
          end
        } iso)
        end
      } iso)

      _manager.send([_c1; _c2], body)

/* A cown encapsulates a piece of state and a message queue.

   state is one-place buffer - this allows us to more easily maintain the iso-ness of the contents
   so that we can send it to behaviours.

   schedulable is used to decide if this cown has been reserved for/or is in use by some behaviour

   msgs is the queue of waiting messages.
*/

interface CownI
  be enqueue(msg: Behaviour tag, response: Promise[Response])
  be commit(ack: Promise[ACK])
  be abort(msg: Behaviour tag, ack: Promise[ACK])

actor Cown[T: Any #send]
  // A triple of state, available and message queue
  let _state: Array[T]
  var _schedulable: Bool
  let _msgs: Array[Behaviour tag]

  // This is None if the cown is not involved in a transaction
  // Otherwise it is the message the cown is waiting to commit
  var _tentative: (Behaviour tag | None)

  new create(state: T) =>
    _state = [ consume state ]
    _schedulable = true
    _msgs = []

    _tentative = None

  // Try to process a waiting message, if successful reserve this cown
  be process() =>
    if not _schedulable then
      return
    end

    try
      _msgs.pop()?.countdown()
      _schedulable = false
    end

  // Enter a transcation, vote yes if this cown is not already part
  // of some transaction
  be enqueue(msg: Behaviour tag, response: Promise[Response]) =>
    if _tentative is None then
      _tentative = msg
      response(YES)
    else
      response(NO)
    end

  // Add the pending message to the message queue
  be commit(ack: Promise[ACK]) =>
    match (_tentative = None)
      | let msg: Behaviour tag =>
          _msgs.unshift(msg)
          ack(ACK)
          process()
    end

  // Abort a transaction. If this cown was waiting to commit the pending
  // message, also throw the message away
  be abort(msg: Behaviour tag, ack: Promise[ACK]) =>
    if _tentative is msg then
      _tentative = None
    end
    ack(ACK)

  // A behaviour is gaining access to this cowns state, send the behaviour
  // the state, leaving this cown empty
  be empty(f: {ref (T)} iso) =>
    try
      f(_state.pop()?)
    end

  // A behaviour is returning some state to this cown
  be fill(state: T) =>
    _state.push(consume state)
    _schedulable = true
    process()