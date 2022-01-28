

use "promises"

primitive YES fun apply(): Bool => true
primitive NO fun apply(): Bool => false
type Response is (YES | NO)

primitive TOKEN

primitive ACK

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

class When[A: Any iso]
  var _c1: Cown[A]

  new create(c1: Cown[A]) =>
    _c1 = c1

  fun _send(b: Behaviour, token: Promise[TOKEN]) =>
    var p = Promise[Response]
    _c1.enqueue(b, p)
    p.next[None]({(commit: Response)(token) =>
      var p = Promise[ACK]
      if commit() then
        _c1.commit(p)
        p.next[None]({(_: ACK) => token(TOKEN)})
      else
        _c1.abort(b, p)
        p.next[None]({(_: ACK) => When[A](_c1)._send(b, token)})
      end
    })

  fun run(f: {ref (A): A^} iso, after: (Promise[TOKEN] | None) = None): Promise[TOKEN] =>
    var body = Behaviour(1, {ref ()(fcell = recover iso [ consume f ] end) =>
      try
        _c1.empty({ref (a: A)(ffcell = recover iso [ fcell.pop()? ] end) =>
          try
            _c1.fill(ffcell.pop()?(consume a))
          end
        } iso)
      end
    } iso)

    var p = Promise[TOKEN]
    match after
      | None => _send(body, p)
      | let after': Promise[TOKEN] => after'.next[None]({(_: TOKEN) => When[A](_c1)._send(body, p)})
    end
    p

  fun op_and[B: Any iso](c2: Cown[B]): _When2[A, B] =>
    _When2[A, B](_c1, c2)

  class _When2[A: Any iso, B: Any iso]
    var _c1: Cown[A]
    var _c2: Cown[B]

    new create(c1: Cown[A], c2: Cown[B]) =>
      _c1 = c1
      _c2 = c2

    fun _send(b: Behaviour, token: Promise[TOKEN]) =>
      var p1 = Promise[Response]
      var p2 = Promise[Response]
      _c1.enqueue(b, p1)
      _c2.enqueue(b, p2)
      Promises[Response].join([p1; p2].values()).next[None]({(responses: Array[Response] val)(token) =>
        var ack1 = Promise[ACK]
        var ack2 = Promise[ACK]
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
      var body = Behaviour(2, {ref ()(fcell = recover iso [ consume f ] end) =>
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
      var p = Promise[TOKEN]
      match after
        | None => _send(body, p)
        | let after': Promise[TOKEN] => after'.next[None]({(_: TOKEN) => _When2[A, B](_c1, _c2)._send(body, p)})
      end
      p

actor Cown[T: Any iso]
  var _state: Array[T]

  var _schedulable: Bool
  var _msgs: Array[Behaviour tag]
  var _tentative: (Behaviour tag | None)
  var _tentative_id: U64

  new create(state: T) =>
    _state = [ consume state ]

    _schedulable = true
    _msgs = []
    _tentative = None
    _tentative_id = 0

  be process() =>
    if not _schedulable then
      return
    end

    try
      _msgs.pop()?.countdown()
      _schedulable = false
    end

  be enqueue(msg: Behaviour tag, response: Promise[Response]) =>
    match _tentative
      | None =>
        _tentative = msg
        response(YES)
    else
      response(NO)
    end

  be commit(ack: Promise[ACK]) =>
    match (_tentative = None)
      | let msg: Behaviour tag =>
          _msgs.unshift(msg)
          ack(ACK)
          process()
    end

  be abort(msg: Behaviour tag, ack: Promise[ACK]) =>
    if _tentative is msg then
      _tentative = None
    end
    ack(ACK)

  be empty(f: {ref (T)} iso) =>
    try
      f(_state.pop()?)
    end

  be fill(state: T) =>
    _state.push(consume state)
    _schedulable = true
    process()