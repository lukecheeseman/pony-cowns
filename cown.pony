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

  fun iso eat(env: Env) =>
    var l = left
    var r = right
    When[Fork iso](l).op_and[Fork iso](r).run({(left: Fork iso, right: Fork iso)(pcell = recover iso [ consume this ] end, env) =>
      left.pick_up()
      right.pick_up()
      try
        var p = pcell.pop()?
        p.hunger = p.hunger - 1
        if p.hunger > 0 then
          (consume p).eat(env)
        else
          env.out.print("Phil " +  p.id.string() + " has finished eating")
        end
      end
      (consume left, consume right)
    })

actor Main
  new create(env: Env) =>
    test1(env)

  fun test1(env: Env) =>
    var f1 = Cown[Fork iso](Fork(1))
    var f2 = Cown[Fork iso](Fork(2))
    var f3 = Cown[Fork iso](Fork(3))
    var f4 = Cown[Fork iso](Fork(4))
    var f5 = Cown[Fork iso](Fork(5))

    Phil(1, f1, f2).eat(env)
    Phil(2, f2, f3).eat(env)
    Phil(3, f3, f4).eat(env)
    Phil(4, f4, f5).eat(env)
    Phil(5, f5, f1).eat(env)

  fun test2(env: Env) =>
    var c1 = Cown[U64Obj iso](U64Obj(10))
    var c2 = Cown[BoolObj iso](BoolObj(true))

    // We have a token to order behaviours, because the the 2pc makes ordering difficult
    // whilst trying to resolve one multimessage, any multimessage can fail and be reattempted
    // but this happens inside of a number of different actors and so there are no causal orderings
    // but we need to do the 2pc for the multimessage to ensure we don't create deadlocking orderings on the cown actor
    // message queueus

    var after = When[U64Obj iso](c1).run({ (x: U64Obj iso) => env.out.print(x.o.string()); consume x })
    after = When[U64Obj iso](c1).run({ (x: U64Obj iso) => x.inc(); env.out.print("inc'd"); consume x }, after)
    after = When[U64Obj iso](c1).run({ (x: U64Obj iso) => env.out.print(x.o.string()); consume x }, after)

    var l = U64Obj(42)
    after = When[U64Obj iso](c1).run({(x: U64Obj iso)(l = consume l) =>
      env.out.print(l.o.string())
      l.inc()
      env.out.print(l.o.string())
      consume x
    })

    //(When[BoolObj iso](c2).op_and[U64Obj iso](c1)).run({ (x: BoolObj iso, y: U64Obj iso) => env.out.print("HI"); (consume x, consume y) }, after)
