module Simple

record Foo : Type where
  MkFoo : (bar : Bool) -> (baz : if bar then Nat else Bool) -> Foo
  
test : Foo
test = MkFoo True Z

test2 : Foo
test2 = MkFoo False True

corecord Foo' : Type where
  bar' : Foo' -> Bool
  baz' : (f : Foo') -> if bar' f then Nat else Bool

test' : Foo'
test' = MkFoo' True Z

test2' : Foo'
test2' = MkFoo' False True

infixr 10 &&&

corecord (&&&) : Type -> Type -> Type where
  left : a &&& b -> a
  right : a &&& b -> b
 
