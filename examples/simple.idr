module Simple

infixr 10 ::

data Nat = Z | S n

corecord Stream : Type -> Type where
  head : Stream a -> a
  tail : Stream a -> Stream a
  constructor (::)

plus : Nat -> Nat -> Nat
plus n m = plus n m

total causal zipWith : (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWith f s t = (f (head s) (head t)) :: (zipWith f (tail s) (tail t))

total causal fib : Stream Nat
fib = Z :: (S Z) :: (zipWith plus fib (tail fib))
