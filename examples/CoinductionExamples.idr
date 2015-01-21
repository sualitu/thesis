module CoinductionExamples

data Nat = Z | S Nat

infixr 10 +
infixr 10 ::

(+) : Nat -> Nat -> Nat
(+) n Z = n
(+) n (S m) = S (n + m)

corecord Stream : Type -> Type where
  head : Stream a -> a
  tail : Stream a -> Stream a
  constructor (::)
  
total causal zeros : Stream Nat
&head zeros = Z
&tail zeros = zeros

total causal repeat : a -> Stream a
&head repeat n = n
&tail repeat n = repeat n

total causal map : (a -> b) -> Stream a -> Stream b
&head map f s = f (head s)
&tail map f s = map f (tail s)

total causal nats : Stream Nat
&head nats = Z
&tail nats = map S nats

total causal zipWith : (a -> b -> c) -> Stream a -> Stream b -> Stream c
&head zipWith f s t = f (head s) (head t)
&tail zipWith f s t = zipWith f (tail s) (tail t)

fst : (a, b) -> a
fst (x, _) = x

snd : (a, b) -> b
snd (_, y) = y

total causal unfold : (s -> (a, s)) -> s -> Stream a
&head unfold step x = fst (step x)
&tail unfold step x = unfold step (snd (step x))

total causal interleave : Stream a -> Stream a -> Stream a
&head interleave s t = head s
&tail interleave s t = interleave t (tail s)

namespace List
  data List : Type -> Type where
    nil : List a
    (::) : a -> List a -> List a

  total causal prepend : List a -> Stream a -> Stream a
  prepend [] s = s
  prepend (x ::xs) s = x :: (prepend xs s)
  
namespace Vect
  data Vect : Nat -> Type -> Type where
    nil : Vect Z a
    (::) : a -> Vect n a -> Vect (S n) a
  
  -- Crashes epsilon
  -- total causal prepend : Vect n a -> Stream a -> Stream a
  -- prepend [] s = s
  -- prepend (x ::xs) s = x :: (prepend xs s)

data Bool = True | False

infixr 10 <=

(<=) : Nat -> Nat -> Bool
(<=) Z _ = True
(<=) (S n) Z = False
(<=) (S n) (S m) = n <= m

-- Crashes epsilon
-- total causal merge : Stream Nat -> Stream Nat -> Stream Nat
-- &head merge s t = case (head s <= head t) of
--                     True  => (head s) 
--                     False => (head t)
-- &tail merge s t = case (head s <= head t) of
--                     True  => case (head t <= head s) of
--                                True  => (merge (tail s) (tail t))
--                                False => (merge (tail s) t)
--                     False => (merge s (tail t))

corecord Tree : Type -> Type where
  value : Tree a -> a
  left  : Tree a -> Tree a
  right : Tree a -> Tree a
  
total causal zerosTree : Tree Nat
&value zerosTree = Z
&left  zerosTree = zerosTree
&right zerosTree = zerosTree

total causal mapTree : (a -> b) -> Tree a -> Tree b
&value mapTree f t = f (value t)
&left  mapTree f t = mapTree f (left  t)
&right mapTree f t = mapTree f (right t)

total causal natTree : Tree Nat
&value natTree = Z
&left  natTree = natTree
&right natTree = mapTree S natTree

total causal calculateWilfully : Tree (Nat, Nat)
calculateWilfully = grow((S Z), (S Z))
  where
    total causal grow : (Nat, Nat) -> Tree(Nat, Nat)
    grow (n, d) = MkTree (n, d) (grow (n, n + d)) (grow (n + d, d))



