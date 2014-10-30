module Test

%default total
{-
data Nat : Type where
  Z : Nat
  S : Nat -> Nat
  
data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a
-}
corecord Stream' : Type -> Type where
  hd : Stream' a -> a
  tl : Stream' b -> Stream' a
  constructor (::)

zeros : Stream' Nat
&hd zeros = Z
&tl zeros = zeros

repeat : a -> Stream' a
&hd repeat a = a
&tl repeat a = repeat a

take' : (n : Nat) -> Stream' a -> Vect n a
take' Z s = []
take' (S k) s = (hd s) :: (take' k (tl s))

instance Functor Stream' where
  map f (hd :: tl) = (f hd) :: (map f tl)

partial
nats : Stream' Nat
&hd nats = Z
&tl nats = map S nats

plus' : Nat -> Nat -> Nat
plus' Z m = m
plus' (S k) m = S (plus' k m)

zipWith' : (a -> b -> c) -> Stream' a -> Stream' b -> Stream' c
&hd zipWith' f s t = f (hd s) (hd t)
&tl zipWith' f s t = zipWith' f (tl s) (tl t)

partial
fib : Stream' Nat
&hd fib = Z
&hd &tl fib = S Z
&tl &tl fib = zipWith' (plus') fib (tl fib)

prepend : Vect n a -> Stream' a -> Stream' a
prepend [] s = s
prepend (x :: xs) s = x :: (prepend xs s)

deStreamCons : Stream' a -> (a, Stream' a)
deStreamCons s = (hd s, tl s)

-- Names are odd. See issues #20
corecord NatStream : Type where
  thd : NatStream -> Nat
  ttl : NatStream -> NatStream
  
deNatStreamCons : NatStream -> (Nat, NatStream)
deNatStreamCons (MkNatStream thd ttl) = (thd, ttl)

zeros' : NatStream
&thd zeros' = Z
&ttl zeros' = zeros'

unfold : (s -> (a, s)) -> s -> Stream' a
&hd unfold step s = fst (step s)
&tl unfold step s = unfold step (snd (step s))

foo : Stream' Nat
foo = unfold deNatStreamCons zeros'

namespace Alpha
  foo : NatStream
  &thd foo = Z
  &ttl foo = foo
