module NoCo

nats : Stream Nat
nats = Z :: map S nats

record Foo : Type where
  MkFoo : (bar : Bool) -> (baz : if bar then Nat else Bool) -> Foo
