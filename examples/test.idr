module Test

corecord Stream' : Type -> Type where
  hd : Stream' a -> a
  tl : Stream' a -> Later' (Stream' a)
  constructor StreamCons

fix : (Later' a -> a) -> a
fix f = f(Next (fix f))

pfix : ((a -> Later' b) -> (a -> b)) -> (a -> b)
pfix f = fix(\g => f (\x => compose {n=Now} g (Next x)))
