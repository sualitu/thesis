module Stream'

f : Type -> Type
f _ = Nat

corecord Stream' : Type -> Type where
  hd : Stream' a -> a
  tl : Stream' (id a) -> Stream' a
  constructor (::)
