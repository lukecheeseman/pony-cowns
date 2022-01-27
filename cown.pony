// The cown needs to either handle the message now or wait until the state is returned
// This could be built on top of actors, but there would need to be a fair amount of communication
// Mostly at the multimessage state?
// Does pony ensure that if i always send in the same acquisition order, then behaviours won't appear out of order?
// I don't think so.

/* Behaviours would need to be actors with a countdown
   - countdown sends a message
   - the variadic arg types would be complicated
*/

/* can the behaviour just be a countdown with a callback to a closure created by the when and the when does the getting the state and returning it */

use "promises"

actor Behaviour
  var _countdown: U64
  var _f: {()} val

  new create(c: U64, f: {()} val) =>
    _countdown = c
    _f = f

  be countdown() =>
    _countdown = _countdown - 1
    if _countdown == 0 then
      _f()
    end

class Cell[T: Any iso]
  var _contents: Array[T] iso
  new iso create(contents: T) => _contents = [consume contents]
  fun ref extract(): T^? => _contents.pop()?

class When[A: Any iso]
  var _c1: Cown[A]

  new create(c1: Cown[A]) =>
    _c1 = c1

  fun _send(b: Behaviour, token: Promise[None]) =>
    var p = Promise[Bool]
    _c1.enqueue(b, p)
    p.next[None]({(commit: Bool) =>
      if not commit then
        _c1.abort()
        When[A](_c1)._send(b, token)
      else
        _c1.commit()
        token(None)
      end
    })

  fun run(f: {(A): A^} val, after: (Promise[None] | None) = None): Promise[None] =>
    var body = Behaviour(1, {()(f) =>
      _c1.empty({(a: A) =>
        _c1.fill(f(consume a))
      })
    })
    var p = Promise[None]
    match after
      | None => _send(body, p)
      | let after': Promise[None] => after'.next[None]({(_: None) => When[A](_c1)._send(body, p)})
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

    fun _send(b: Behaviour, token: Promise[None]) =>
      var p = Promise[Bool]
      _c1.enqueue(b, p)
      _c2.enqueue(b, p)
      p.next[None]({(commit: Bool) =>
        if not commit then
          _c1.abort()
          _c2.abort()
          _When2[A, B](_c1, _c2)._send(b, token)
        else
          _c1.commit()
          _c2.commit()
          token(None)
        end
      })

    fun run(f: {(A, B): (A^, B^)} val, after: (Promise[None] | None) = None) =>
      var body = Behaviour(2, {()(f) =>
        _c1.empty({ref (a: A)(_c1 = _c1, _c2 = _c2, f) =>
          _c2.empty({ref (b: B)(a = Cell[A](consume a)) =>
            try
              (let a', let b') = f(a.extract()? , consume b)
              _c1.fill(consume a')
              _c2.fill(consume b')
            end
          })
        })
      })
      var p = Promise[None]
      match after
        | None => _send(body, p)
        | let after': Promise[None] => after'.next[None]({(_: None) => _When2[A, B](_c1, _c2)._send(body, p)})
      end
      p

actor Cown[T: Any iso]
  // abuse a single space array to indicate the presence
  // of state
  var _state: Array[T]
  var _schedulable: Bool

  var _msgs: Array[Behaviour tag]
  var _tentative: (Behaviour tag | None)

  new create(state: T) =>
    _state = [ consume state ]
    _schedulable = true
    _msgs = []
    _tentative = None

  fun ref process() =>
    if not _schedulable then
      return
    end

    try
      var msg = _msgs.pop()?
      msg.countdown()
      _schedulable = false
    end

  be enqueue(msg: Behaviour tag, response: Promise[Bool]) =>
    match _tentative
      | None =>
        _tentative = msg
        response(true)
    else
      response(false)
    end

  be commit() =>
    match (_tentative = None)
      | let msg: Behaviour tag =>
          _msgs.unshift(msg)
          process()
    end

  be abort() =>
    _tentative = None

  be empty(f: {ref (T)} iso) =>
    try
      f(_state.pop()?)
      _schedulable = true
    end

  be fill(state: T) =>
    _state.push(consume state)
    process()

class U64Obj
  var o: U64
  new iso create(o': U64) => o = o'
  fun ref inc() => o = o + 1

class BoolObj
  var o: Bool
  new iso create(o': Bool) => o = o'
  fun ref neg() => o = not o

actor Main
  new create(env: Env) =>
    var c1 = Cown[U64Obj iso](recover U64Obj(10) end)
    var c2 = Cown[BoolObj iso](recover BoolObj(true) end)

    // We have a token to order behaviours, because the the 2pc makes ordering difficult
    // whilst trying to resolve one multimessage, any multimessage can fail and be reattempted
    // but this happens inside of a number of different actors and so there are no causal orderings
    // but we need to do the 2pc for the multimessage to ensure we don't create deadlocking orderings on the cown actor
    // message queueus

    var after = When[U64Obj iso](c1).run({ (x: U64Obj iso) => env.out.print(x.o.string()); consume x })
    after = When[U64Obj iso](c1).run({ (x: U64Obj iso) => x.inc(); consume x }, after)
    after = When[U64Obj iso](c1).run({ (x: U64Obj iso) => env.out.print(x.o.string()); consume x }, after)

    (When[BoolObj iso](c2).op_and[U64Obj iso](c1)).run({ (x: BoolObj iso, y: U64Obj iso) => env.out.print("HI"); (consume x, consume y) }, after)