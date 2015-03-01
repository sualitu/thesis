module Simple

infixr 10 ::

data Nat = Z | S n

data List : Type -> Type where
  Nil : List a
  Cons : a -> List a -> List a

corecord Stream a where
  head : a
  tail : Stream a
  constructor (::)

corecord BisimStream a (s : Stream a) (t : Stream a) where
   phead : head s = head t
   ptail : BisimStream a (tail s) (tail t)

record Foo a where
  xs : List a
