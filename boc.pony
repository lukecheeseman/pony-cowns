

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

/* A when (and its related When<N>) serves as a transcation manager between cowns
   The when takes a cown and if further cowns are required by the 'n' method then constructs a when
   which managers 1 more cown.

   When the run builder is called, the method constructs a sequence of nested lambdas that
   each "partially apply" the provided lambda that takes all the cowns.

   We know that at the point of running the behaviour and emptying the state, that each cown has
   reserved itself for this behaviour.

   The final layer calls the user provided lambda with all the pieces of state and then
   returns the state from the callback to each cown as necessary.

   If a token for ordering is provided we wait until the token is fulfilled, otherwise
   we got straigh ahead to trying to send the behaviour to all of the cowns. This
   is essentially 2pc.
*/
class When[A: Any iso]
  let _c1: Cown[A]

  new create(c1: Cown[A]) =>
    _c1 = c1

  fun _send(b: Behaviour, token: Promise[TOKEN]) =>
    let p = Promise[Response]
    _c1.enqueue(b, p)
    p.next[None]({(commit: Response)(token) =>
      let p = Promise[ACK]
      if commit() then
        _c1.commit(p)
        p.next[None]({(_: ACK) => token(TOKEN)})
      else
        _c1.abort(b, p)
        p.next[None]({(_: ACK) => When[A](_c1)._send(b, token)})
      end
    })

  fun run(f: {ref (A): A^} iso, after: (Promise[TOKEN] | None) = None): Promise[TOKEN] =>
    // We need to maintain the iso-ness of the function so we abuse an array to pop the function
    // in and out of the array
    let body = Behaviour(1, {ref ()(fcell = recover iso [ consume f ] end) =>
      try
        _c1.empty({ref (a: A)(ffcell = recover iso [ fcell.pop()? ] end) =>
          try
            _c1.fill(ffcell.pop()?(consume a))
          end
        } iso)
      end
    } iso)

    let p = Promise[TOKEN]
    match after
      | None => _send(body, p)
      | let after': Promise[TOKEN] => after'.next[None]({(_: TOKEN) => When[A](_c1)._send(body, p)})
    end
    p

  fun n[B: Any iso](c2: Cown[B]): _When2[A, B] =>
    _When2[A, B](_c1, c2)

  // A when over 2 cowns
  class _When2[A: Any iso, B: Any iso]
    let _c1: Cown[A]
    let _c2: Cown[B]

    new create(c1: Cown[A], c2: Cown[B]) =>
      _c1 = c1
      _c2 = c2

    fun _send(b: Behaviour, token: Promise[TOKEN]) =>
      let p1 = Promise[Response]
      let p2 = Promise[Response]
      _c1.enqueue(b, p1)
      _c2.enqueue(b, p2)
      Promises[Response].join([p1; p2].values()).next[None]({(responses: Array[Response] val)(token) =>
        let ack1 = Promise[ACK]
        let ack2 = Promise[ACK]
        for commit in responses.values() do
          if not commit() then
            _c1.abort(b, ack1)
            _c2.abort(b, ack2)
            Promises[ACK].join([ack1; ack2].values()).next[None]({(_: Array[ACK] val) =>
              _When2[A, B](_c1, _c2)._send(b, token)
            })
            return
          end
        end
        _c1.commit(ack1)
        _c2.commit(ack2)
        Promises[ACK].join([ack1; ack2].values()).next[None]({(_: Array[ACK] val) =>
          token(TOKEN)
          })
        })

    fun run(f: {ref (A, B): (A^, B^)} iso, after: (Promise[TOKEN] | None) = None) =>
      let body = Behaviour(2, {ref ()(fcell = recover iso [ consume f ] end) =>
        try
        _c1.empty({ref (a: A)(ffcell = recover iso [ fcell.pop()? ] end, _c2 = _c2) =>
          try
          _c2.empty({ref (b: B)(facell = recover iso [ (ffcell.pop()?, consume a) ] end, _c1 = _c1) =>
            try
              (let f, let a) = facell.pop()?
              (let a', let b') = f(consume a, consume b)
              _c1.fill(consume a')
              _c2.fill(consume b')
            end
          } iso)
          end
        } iso)
        end
      } iso)
      let p = Promise[TOKEN]
      match after
        | None => _send(body, p)
        | let after': Promise[TOKEN] => after'.next[None]({(_: TOKEN) => _When2[A, B](_c1, _c2)._send(body, p)})
      end
      p

/* A cown encapsulates a piece of state and a message queue.

   state is one-place buffer - this allows us to more easily maintain the iso-ness of the contents
   so that we can send it to behaviours.

   schedulable is used to decide if this cown has been reserved for/or is in use by some behaviour

   msgs is the queue of waiting messages.
*/
actor Cown[T: Any iso]
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