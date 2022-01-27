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
  var _f: {ref ()} iso

  new create(c: U64, f: {ref ()} iso) =>
    _countdown = c
    _f = consume f

  be countdown() =>
    _countdown = _countdown - 1
    if _countdown == 0 then
      _f()
    end

class Cell[T: Any iso]
  var _contents: Array[T] iso
  new iso create(contents: T) => _contents = [consume contents]
  fun ref extract(): T^? => _contents.pop()?

class Behaviour1[A: Any iso]
  var c1: Cown[A]
  var f: Array[{ref (A): A^} iso]
  var a: Array[A]

  new iso create(c1': Cown[A], f': {ref (A): A^} iso) =>
    c1 = c1'
    f = [consume f']
    a = []

  fun ref with_a(a': A) => a.unshift(consume a')

  fun ref apply() =>
    try
      c1.fill(f.pop()?(a.pop()?))
    end

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

  fun run(f: {ref (A): A^} iso, after: (Promise[None] | None) = None): Promise[None] =>
    var be1 = Behaviour1[A].create(_c1, consume f)
    var body = Behaviour(1, {ref ()(be1cell = recover iso [ consume be1 ] end) =>
      try
        var be1 = be1cell.pop()?
        _c1.empty({ref (a: A)(be1 = consume be1) =>
          be1.>with_a(consume a).>apply()
        } iso)
      end
    } iso)
    var p = Promise[None]
    match after
      | None => _send(body, p)
      | let after': Promise[None] => after'.next[None]({(_: None) => When[A](_c1)._send(body, p)})
    end
    p

  /*
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
      p*/

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

// Using the API past here

class U64Obj
  var o: U64
  new iso create(o': U64) => o = o'
  fun ref inc() => o = o + 1

class BoolObj
  var o: Bool
  new iso create(o': Bool) => o = o'
  fun ref neg() => o = not o

class Fork
  var id: U64
  var count: U64
  
  new iso create(id': U64) =>
    id = id'
    count = 0
  
  fun ref pick_up() => count = count + 1

class Phil
  var id: U64
  var hunger: U64
  var left: Cown[Fork iso]
  var right: Cown[Fork iso]

  new iso create(id': U64, left': Cown[Fork iso], right': Cown[Fork iso]) =>
    id = id'
    hunger = 10
    left = left'
    right = right'

  /*
  fun iso _eat(p: Phil iso) =>
    When[Fork iso](left).op_and[Fork iso](right).run({ref (left: Fork iso, right: Fork iso)(p = consume p) =>
      left.pick_up()
      right.pick_up()
      p.eat()
      (consume left, consume right)
    })*/
/*
  fun iso eat() =>
    var l = left
    var r = right
    When[Fork iso](l).op_and[Fork iso](r).run({iso (left: Fork iso, right: Fork iso)(p: Phil iso = consume this) =>
      left.pick_up()
      right.pick_up()
      (consume this).p.eat()
      (consume left, consume right)
    })

  fun iso eat() =>
    When[Fork iso](left).op_and[Fork iso](right).run({iso (left: Fork iso, right: Fork iso)(l) =>
      left.pick_up()
      right.pick_up()
      (consume left, consume right)
    })
*/

actor Main
  new create(env: Env) =>
    test2(env)

/*
  fun test1(env: Env) =>
    var f1 = Cown[Fork iso](Fork(1))
    var f2 = Cown[Fork iso](Fork(2))
    var f3 = Cown[Fork iso](Fork(3))
    var f4 = Cown[Fork iso](Fork(4))
    var f5 = Cown[Fork iso](Fork(5))
  
    Phil(1, f1, f2).eat()
    Phil(2, f2, f3).eat()
    Phil(3, f3, f4).eat()
    Phil(4, f4, f5).eat()
    Phil(5, f5, f1).eat()
*/

  fun test2(env: Env) =>
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

    var l = U64Obj(42)
    after = When[U64Obj iso](c1).run({ref (x: U64Obj iso)(l = consume l) =>
      env.out.print(l.o.string())
      l.inc()
      env.out.print(l.o.string())
      consume x 
    } iso)

    //(When[BoolObj iso](c2).op_and[U64Obj iso](c1)).run({ (x: BoolObj iso, y: U64Obj iso) => env.out.print("HI"); (consume x, consume y) }, after)
