module Test

import Data.Vect

namespace GuardedRecursion
  ||| A computation that is available later.
  data Later' : Type -> Type where
    Next : {a : Type} -> a -> Later' a

  data Forall : Type -> Type where
    LambdaKappa : {a : Type} -> a -> Forall a
 
  apply : {a : Type} -> Forall a -> a
  apply (LambdaKappa a) = a 

  data Availability = Now | Tomorrow Availability

  Later : Availability -> Type -> Type
  Later Now a = a
  Later (Tomorrow n) a = Later' (Later n a)
  
  laterDist : Later' (a -> b) -> (Later' a -> Later' b)
  laterDist (Next f) = \a => case a of
                               (Next a') => Next (f a')
                               
  compose : {a, b : Type} -> 
            {n : Availability} -> 
            Later (Tomorrow n) (a -> b) -> 
            Later (Tomorrow n) a -> 
            Later (Tomorrow n) b
  compose {n = Now} t u = compose' t u
    where
     compose' : {a, b : Type} -> Later' (a -> b) -> Later' a -> Later' b
     compose' (Next t) (Next u) = Next (t u)
  compose {n = Tomorrow n'} (Next t) (Next u) = Next (compose {n = n'} t u)

  liftCompose : {a, b : Type} -> Later' (a -> b) -> (a -> Later' b)
  liftCompose f = \x : a => compose {n = Now} f (Next x)

StreamCons : a -> Later' (Stream a) -> Stream a
StreamCons a (Next s) = a :: s

tl : Stream a -> Later' (Stream a)
tl (_ :: s) = Next s

fix : (Later' a -> a) -> a
fix f = f(Next (fix f))

mutual
  cycle : (Later' (Nat -> Nat -> Stream Nat)) -> Nat -> Nat -> Stream Nat
  cycle rec Z m = StreamCons Z (compose {n=Now} (compose {n=Now} rec (Next m)) (Next m))
  cycle rec (S n) m = StreamCons (S n) (compose {n=Now} (compose {n=Now} rec (Next n)) (Next m))

  cycle' : Forall (Nat -> Nat -> Stream Nat)
  cycle' = LambdaKappa (fix(\rec, n, m => cycle rec n m))
    
mutual 
  prepend : (Later' (Vect n a -> Stream a -> Stream a)) -> Vect n a -> Stream a -> Stream a
  prepend rec [] s = s 
  prepend rec (x :: xs) s = StreamCons x (compose {n=Now} (compose {n=Now} rec (Next xs)) (Next s))

  prepend' : Forall (Vect n a -> Stream a -> Stream a)
  prepend' = LambdaKappa (fix(\rec, xs, s => prepend rec xs s))
