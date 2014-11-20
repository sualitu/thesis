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

mutual
  corecord Alpha : Type where
    bravo : Alpha -> (if test3 then Bool else Nat)
    
  test3 : Bool
  test3 = True
 

