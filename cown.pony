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

class When[A: Any iso]
  var _c1: Cown[A]

  new create(c1: Cown[A]) =>
    _c1 = c1

  fun run(f: {(A)} val) =>
    var body = Behaviour(1, {()(f) =>
      _c1.empty({(a: A) =>
        //f(a)
        _c1.fill(consume a)
      })
    })
    _c1.send(body)
/*
  fun op_and[B: Any iso](c2: Cown[B]): _When2[A, B] =>
    _When2[A, B](_c1, c2)

  class _When2[A: Any iso, B: Any iso]
    var _c1: Cown[A]
    var _c2: Cown[B]

    new create(c1: Cown[A], c2: Cown[B]) =>
      _c1 = c1
      _c2 = c2

    fun run(f: {(A, B)} val) =>
      var body = Behaviour(2, {()(f) =>
        _c1.empty({(a: A)(_c1 = _c1, _c2 = _c2, f) =>
          _c2.empty({(b: B)(a = consume a) =>
            //f(a, b)
            _c2.fill(consume b)
            _c1.fill(consume a)
          })
        })
      })
      _c1.send(body)
      _c2.send(body)
*/

actor Cown[T: Any iso]
  // abuse a single space array to indicate the presence
  // of state
  var _state: Array[T]
  var _schedulable: Bool

  var _msgs: Array[Behaviour tag]

  new create(state: T) =>
    _state = [ consume state ]
    _schedulable = true
    _msgs = []

  fun ref process() =>
    if not _schedulable then
      return
    end

    try
      var msg = _msgs.pop()?
      msg.countdown()
      _schedulable = false
    end

  be send(msg: Behaviour tag) =>
    _msgs.unshift(msg)
    process()

  be empty(f: {(T)} val) =>
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

    When[U64Obj iso](c1).run({ (x: U64Obj) => env.out.print(x.o.string()) })
    When[U64Obj iso](c1).run({ (x: U64Obj) => x.inc() })
    When[U64Obj iso](c1).run({ (x: U64Obj) => env.out.print(x.o.string()) })

    //(When[BoolObj iso](c2).op_and[U64Obj iso](c1)).run({ (x: BoolObj, y: U64Obj) => env.out.print("HI") })