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

    // Put the Phil ins a cell as we need to keep it as an iso to propogate forwards, but if we capture the phil
    // then it becomes a field of the object literal lambda
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