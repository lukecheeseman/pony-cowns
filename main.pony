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

  fun iso eat(m: Manager, env: Env) =>
    // we consume this so we need to get left and right out first, but these are tag so it's fine
    var l = left
    var r = right

    // Put the Phil ins a cell as we need to keep it as an iso to propogate forwards, but if we capture the phil
    // then it becomes a field of the object literal lambda
    m.when[Fork iso](l).n[Fork iso](r).run({(left, right)(pcell = recover iso [ consume this ] end) =>
      left.pick_up()
      right.pick_up()
      try
        var p = pcell.pop()?
        p.hunger = p.hunger - 1
        if p.hunger > 0 then
          (consume p).eat(m, env)
        else
          env.out.print("Phil " +  p.id.string() + " has finished eating")
        end
      end
      (consume left, consume right)
    })

actor Main
  new create(env: Env) =>
    test4(env)

  fun test1(env: Env) =>
    Start({(m: Manager)(env) =>
      env.out.print("started")
      var f1 = Cown[Fork iso](Fork(1))
      var f2 = Cown[Fork iso](Fork(2))
      var f3 = Cown[Fork iso](Fork(3))
      var f4 = Cown[Fork iso](Fork(4))
      var f5 = Cown[Fork iso](Fork(5))

      Phil(1, f1, f2).eat(m, env)
      Phil(2, f2, f3).eat(m, env)
      Phil(3, f3, f4).eat(m, env)
      Phil(4, f4, f5).eat(m, env)
      Phil(5, f5, f1).eat(m, env)
    })

  fun test2(env: Env) =>
    Start({(m: Manager)(env) =>
      env.out.print("started")

      var c1 = Cown[U64Obj iso](U64Obj(10))
      var c2 = Cown[BoolObj iso](BoolObj(true))

      // We have a token to order behaviours, because the the 2pc makes ordering difficult
      // whilst trying to resolve one multimessage, any multimessage can fail and be reattempted
      // but this happens inside of a number of different actors and so there are no causal orderings
      // but we need to do the 2pc for the multimessage to ensure we don't create deadlocking orderings on the cown actor
      // message queueus

      m.when[U64Obj iso](c1).run({(x) => env.out.print(x.o.string()); x})
      m.when[U64Obj iso](c1).run({(x) => x.inc(); env.out.print("inc'd"); x})
      m.when[U64Obj iso](c1).run({(x) => env.out.print(x.o.string()); x})

      m.when[BoolObj iso](c2).run({(z) => env.out.print("It's a bool!"); z})

      var l = U64Obj(42)
      m.when[U64Obj iso](c1).run({(x)(l = consume l) =>
        env.out.print(l.o.string())
        l.inc()
        env.out.print(l.o.string())
        x
      })

      m.when[BoolObj iso](c2).n[U64Obj iso](c1).run({ (x, y) =>
        env.out.print(if x.o then "true" else "false" end + " and " + y.o.string())
        (consume x, consume y)
      })
    })

  fun test3(env: Env) =>
    Start({(m: Manager)(env) =>
      // Either print can happen first
      var c1 = Cown[U64Obj iso](U64Obj(10))
      var c2 = Cown[U64Obj iso](U64Obj(10))
      var c3 = Cown[U64Obj iso](U64Obj(10))

      m.when[U64Obj iso](c1).run({(x)(env) =>
        m.when[U64Obj iso](c3).run({(x) =>
          env.out.print("{c1, c3}")
          env.out.print(x.o.string())
          x.inc()
          x
        })
        x
      })

      m.when[U64Obj iso](c2).run({(x) (env)=>
        m.when[U64Obj iso](c3).run({(x) =>
          env.out.print("{c2, c3}")
          env.out.print(x.o.string())
          x
        })
        x
      })
    })

    fun test4(env: Env) =>
      Start({(m: Manager)(env) =>
        let first = Cown[Fork iso](Fork(1))
        var prev = first

        let limit: U64 = 1000
        var i: U64 = 0
        while (i < limit) do
          var next = Cown[Fork iso](Fork(i + 2))
          Phil(i, prev, next).eat(m, env)
          prev = next
          i = i + 1
        end
      })