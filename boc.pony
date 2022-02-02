use "promises"

// Tokens for voting on commit
primitive _YES fun apply(): Bool => true
primitive _NO fun apply(): Bool => false
type _Response is (_YES | _NO)

// Token for acking commit/abort
primitive _ACK

/* A behaviour is an actor that encapsulates a coutdown and a callback that is
   the body of the behaviours.
   Once the coutdown hits zero, the callback is called
*/

primitive Start
  fun apply(f: {(Manager)}) => f(Manager._create())

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

actor Manager
  let _msgs: Array[(Array[CownI tag] val, Behaviour)]
  var _processing: Array[CownI tag]

  new _create() =>
    _msgs = []
    _processing = []

  be _send(cowns: Array[CownI tag] val, b: Behaviour) =>
    _msgs.unshift((cowns, b))
    _process()

  fun ref _clear(cowns: Array[CownI tag] val) =>
    for cown in cowns.values() do
      try
        _processing.delete(_processing.find(cown)?)?
      end
    end

  // Log the result of a transaction and clear the cowns from processing
  be _abort(cowns: Array[CownI tag] val, b: Behaviour) =>
    // The send failed so push the message back on the front of the queue and try again
    _msgs.push((cowns, b))
    _clear(cowns)
    _process()

  be _commit(cowns: Array[CownI tag] val) =>
    _clear(cowns)
    _process()

  fun tag _send_abort(cowns: Array[CownI tag] val, b: Behaviour) =>
    var acks = Array[Promise[_ACK]]
    for cown in cowns.values() do
      let ack = Promise[_ACK]
      acks.push(ack)
      cown._abort(b, ack)
    end

    Promises[_ACK].join(acks.values()).next[None]({(_: Array[_ACK] val)(m: Manager tag = this) =>
      m._abort(cowns, b)
    })

  fun tag _send_commit(cowns: Array[CownI tag] val) =>
    var acks = Array[Promise[_ACK]]
    for cown in cowns.values() do
      let ack = Promise[_ACK]
      acks.push(ack)
      cown._commit(ack)
    end

    Promises[_ACK].join(acks.values()).next[None]({(_: Array[_ACK] val)(m: Manager tag = this) =>
      m._commit(cowns)
    })

  // Attempt to process a message, abort if we overlap with any cown that is already
  // being processed
  fun ref _process() =>
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
      let responses = Array[Promise[_Response]]
      for cown in cowns.values() do
        let response = Promise[_Response]
        cown._enqueue(b, response)
        responses.push(response)
      end
      Promises[_Response].join(responses.values()).next[None]({(responses: Array[_Response] val)(m: Manager tag=this) =>
        for commit in responses.values() do
          if not commit() then
            m._send_abort(cowns, b)
            return
          end
        end
        m._send_commit(cowns)
      })
    end

  fun tag when[A: Any #send](c1: Cown[A]): _When1[A] =>
    _When1[A]._create(this, c1)

  class _When1[A: Any #send]
    let _manager: Manager
    let _c1: Cown[A]

    new _create(manager: Manager tag, c1: Cown[A]) =>
      _manager = manager
      _c1 = c1

    fun run(f: {ref (A): (A^)} iso) =>
      let body = Behaviour(1, {ref ()(cell = recover iso [ consume f ] end) =>
        try
          (let f) = cell.pop()?
          _c1._empty({ref (a: A)(cell = recover iso [ (consume f) ] end, _c1 = _c1) =>
            try
              (let f) = cell.pop()?
              (let a') = f(consume a)
              _c1._fill(consume a')
            end
          } iso)
        end
      } iso)
      _manager._send([_c1], body)

    fun n[B: Any #send](c2: Cown[B]): _When2[A, B] =>
      _When2[A, B]._create(_manager, _c1, c2)

  class _When2[A: Any #send, B: Any #send]
    let _manager: Manager
    let _c1: Cown[A]
    let _c2: Cown[B]

    new _create(manager: Manager tag, c1: Cown[A], c2: Cown[B]) =>
      _manager = manager
      _c1 = c1
      _c2 = c2

    fun run(f: {ref (A, B): (A^, B^)} iso) =>
      let body = Behaviour(2, {ref ()(cell = recover iso [ consume f ] end) =>
        try
          (let f) = cell.pop()?
          _c1._empty({ref (a: A)(cell = recover iso [ (consume f) ] end, _c1 = _c1, _c2 = _c2) =>
            try
              (let f) = cell.pop()?
              _c2._empty({ref (b: B)(cell = recover iso [ (consume f, consume a) ] end, _c1 = _c1, _c2 = _c2) =>
                try
                  (let f, let a) = cell.pop()?
                  (let a', let b') = f(consume a, consume b)
                  _c1._fill(consume a')
                  _c2._fill(consume b')
                end
              } iso)
            end
          } iso)
        end
      } iso)
      _manager._send([_c1; _c2], body)

    fun n[C: Any #send](c3: Cown[C]): _When3[A, B, C] =>
      _When3[A, B, C]._create(_manager, _c1, _c2, c3)

  class _When3[A: Any #send, B: Any #send, C: Any #send]
    let _manager: Manager
    let _c1: Cown[A]
    let _c2: Cown[B]
    let _c3: Cown[C]

    new _create(manager: Manager tag, c1: Cown[A], c2: Cown[B], c3: Cown[C]) =>
      _manager = manager
      _c1 = c1
      _c2 = c2
      _c3 = c3

    fun run(f: {ref (A, B, C): (A^, B^, C^)} iso) =>
      let body = Behaviour(3, {ref ()(cell = recover iso [ consume f ] end) =>
        try
          (let f) = cell.pop()?
          _c1._empty({ref (a: A)(cell = recover iso [ (consume f) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3) =>
            try
              (let f) = cell.pop()?
              _c2._empty({ref (b: B)(cell = recover iso [ (consume f, consume a) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3) =>
                try
                  (let f, let a) = cell.pop()?
                  _c3._empty({ref (c: C)(cell = recover iso [ (consume f, consume a, consume b) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3) =>
                    try
                      (let f, let a, let b) = cell.pop()?
                      (let a', let b', let c') = f(consume a, consume b, consume c)
                      _c1._fill(consume a')
                      _c2._fill(consume b')
                      _c3._fill(consume c')
                    end
                  } iso)
                end
              } iso)
            end
          } iso)
        end
      } iso)
      _manager._send([_c1; _c2; _c3], body)

    fun n[D: Any #send](c4: Cown[D]): _When4[A, B, C, D] =>
      _When4[A, B, C, D]._create(_manager, _c1, _c2, _c3, c4)

  class _When4[A: Any #send, B: Any #send, C: Any #send, D: Any #send]
    let _manager: Manager
    let _c1: Cown[A]
    let _c2: Cown[B]
    let _c3: Cown[C]
    let _c4: Cown[D]

    new _create(manager: Manager tag, c1: Cown[A], c2: Cown[B], c3: Cown[C], c4: Cown[D]) =>
      _manager = manager
      _c1 = c1
      _c2 = c2
      _c3 = c3
      _c4 = c4

    fun run(f: {ref (A, B, C, D): (A^, B^, C^, D^)} iso) =>
      let body = Behaviour(4, {ref ()(cell = recover iso [ consume f ] end) =>
        try
          (let f) = cell.pop()?
          _c1._empty({ref (a: A)(cell = recover iso [ (consume f) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3, _c4 = _c4) =>
            try
              (let f) = cell.pop()?
              _c2._empty({ref (b: B)(cell = recover iso [ (consume f, consume a) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3, _c4 = _c4) =>
                try
                  (let f, let a) = cell.pop()?
                  _c3._empty({ref (c: C)(cell = recover iso [ (consume f, consume a, consume b) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3, _c4 = _c4) =>
                    try
                      (let f, let a, let b) = cell.pop()?
                      _c4._empty({ref (d: D)(cell = recover iso [ (consume f, consume a, consume b, consume c) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3, _c4 = _c4) =>
                        try
                          (let f, let a, let b, let c) = cell.pop()?
                          (let a', let b', let c', let d') = f(consume a, consume b, consume c, consume d)
                          _c1._fill(consume a')
                          _c2._fill(consume b')
                          _c3._fill(consume c')
                          _c4._fill(consume d')
                        end
                      } iso)
                    end
                  } iso)
                end
              } iso)
            end
          } iso)
        end
      } iso)
      _manager._send([_c1; _c2; _c3; _c4], body)

    fun n[E: Any #send](c5: Cown[E]): _When5[A, B, C, D, E] =>
      _When5[A, B, C, D, E]._create(_manager, _c1, _c2, _c3, _c4, c5)

  class _When5[A: Any #send, B: Any #send, C: Any #send, D: Any #send, E: Any #send]
    let _manager: Manager
    let _c1: Cown[A]
    let _c2: Cown[B]
    let _c3: Cown[C]
    let _c4: Cown[D]
    let _c5: Cown[E]

    new _create(manager: Manager tag, c1: Cown[A], c2: Cown[B], c3: Cown[C], c4: Cown[D], c5: Cown[E]) =>
      _manager = manager
      _c1 = c1
      _c2 = c2
      _c3 = c3
      _c4 = c4
      _c5 = c5

    fun run(f: {ref (A, B, C, D, E): (A^, B^, C^, D^, E^)} iso) =>
      let body = Behaviour(5, {ref ()(cell = recover iso [ consume f ] end) =>
        try
          (let f) = cell.pop()?
          _c1._empty({ref (a: A)(cell = recover iso [ (consume f) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3, _c4 = _c4, _c5 = _c5) =>
            try
              (let f) = cell.pop()?
              _c2._empty({ref (b: B)(cell = recover iso [ (consume f, consume a) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3, _c4 = _c4, _c5 = _c5) =>
                try
                  (let f, let a) = cell.pop()?
                  _c3._empty({ref (c: C)(cell = recover iso [ (consume f, consume a, consume b) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3, _c4 = _c4, _c5 = _c5) =>
                    try
                      (let f, let a, let b) = cell.pop()?
                      _c4._empty({ref (d: D)(cell = recover iso [ (consume f, consume a, consume b, consume c) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3, _c4 = _c4, _c5 = _c5) =>
                        try
                          (let f, let a, let b, let c) = cell.pop()?
                          _c5._empty({ref (e: E)(cell = recover iso [ (consume f, consume a, consume b, consume c, consume d) ] end, _c1 = _c1, _c2 = _c2, _c3 = _c3, _c4 = _c4, _c5 = _c5) =>
                            try
                              (let f, let a, let b, let c, let d) = cell.pop()?
                              (let a', let b', let c', let d', let e') = f(consume a, consume b, consume c, consume d, consume e)
                              _c1._fill(consume a')
                              _c2._fill(consume b')
                              _c3._fill(consume c')
                              _c4._fill(consume d')
                              _c5._fill(consume e')
                            end
                          } iso)
                        end
                      } iso)
                    end
                  } iso)
                end
              } iso)
            end
          } iso)
        end
      } iso)
      _manager._send([_c1; _c2; _c3; _c4; _c5], body)

/* A cown encapsulates a piece of state and a message queue.

   state is one-place buffer - this allows us to more easily maintain the iso-ness of the contents
   so that we can send it to behaviours.

   schedulable is used to decide if this cown has been reserved for/or is in use by some behaviour

   msgs is the queue of waiting messages.
*/

interface CownI
  be _enqueue(msg: Behaviour tag, response: Promise[_Response])
  be _commit(ack: Promise[_ACK])
  be _abort(msg: Behaviour tag, ack: Promise[_ACK])

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
  be _process() =>
    if not _schedulable then
      return
    end

    try
      _msgs.pop()?.countdown()
      _schedulable = false
    end

  // Enter a transcation, vote yes if this cown is not already part
  // of some transaction
  be _enqueue(msg: Behaviour tag, response: Promise[_Response]) =>
    if _tentative is None then
      _tentative = msg
      response(_YES)
    else
      response(_NO)
    end

  // Add the pending message to the message queue
  be _commit(ack: Promise[_ACK]) =>
    match (_tentative = None)
      | let msg: Behaviour tag =>
          _msgs.unshift(msg)
          ack(_ACK)
          _process()
    end

  // Abort a transaction. If this cown was waiting to commit the pending
  // message, also throw the message away
  be _abort(msg: Behaviour tag, ack: Promise[_ACK]) =>
    if _tentative is msg then
      _tentative = None
    end
    ack(_ACK)

  // A behaviour is gaining access to this cowns state, send the behaviour
  // the state, leaving this cown empty
  be _empty(f: {ref (T)} iso) =>
    try
      f(_state.pop()?)
    end

  // A behaviour is returning some state to this cown
  be _fill(state: T) =>
    _state.push(consume state)
    _schedulable = true
    _process()