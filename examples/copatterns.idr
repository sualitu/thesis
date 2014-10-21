-- Streams

codata Stream : Type -> Type where
  head : Stream a -> a
  tail : Stream a -> Stream a
  constructor (::)

map : (a -> b) -> Stream a -> Stream b
head map f s = f (head s)
tail map f s = map f (tail s)

foldln : Nat -> (a -> b -> a) -> a -> Stream b -> a
foldln Z     f a s = a
foldln (S n) f a s = foldln f (f a (head s)) (tail s)

iterate : (a -> a) -> a -> Stream a
head iterate f a = a
tail iterate f a = iterate f (f a)

nats : Stream Nat
head nats = Z
tail nats = map S nats

repeat : a -> Stream a
head repeat a = a
tail repeat a = repeat a

cycle : Vect (S n) a -> Stream a
cycle xs = cycle' xs xs
  where cycle' : Vect (S n) a -> Vect m a -> Stream a
        head cycle' (x :: xs)       []  = x
        head cycle'       xs  (y :: ys) = y
        tail cycle' (x :: xs)       []  = cycle' (x :: xs) xs
        tail cycle'       xs  (y :: ys) = cycle' xs ys

take : (n : Nat) -> Stream a -> Vect n a
take Z     _ = []
take (S n) s = (head s) :: (take n (tail s))

drop : Nat -> Stream a -> Stream a
drop Z     s = s
drop (S n) s = drop n (tail s)

index : Nat -> Stream a -> a
index    Z  s = head s
index (S n) s = index n (tail s)

zip : Stream a -> Stream b -> Stream (a, b)
head zip s t = (head s, head t)
tail zip s t = zip (tail s) (tail t)

zipWith : (a -> b -> c) -> Stream a -> Stream b -> Stream c
head zipWith f s t = f (head s) (head t)
tail zipWith f s t = zipWith f (tail s) (tail t)

unzip : Stream (a, b) -> (Stream a, Stream b)
unzip s = (map fst s, map snd s)

intersect : Stream a -> Stream a -> Stream a
head      intersect s t = head s
head tail intersect s t = head t
tail tail intersect s t = intersect (tail s) (tail t)

scanl : (a -> b -> a) -> a -> Stream b -> Stream a
head scanl f a s = a
tail scanl f a s = scanl f (f a (head s)) (tail s)

prepend : Vect n a -> Stream a -> Stream a
head prepend []        s = head s
head prepend (x :: xs) s = x
tail prepend []        s = tail s
tail prepend (x :: xs) s = prepend xs s

cons : a -> Stream a -> Stream a
head cons a s = a
tail cons a s = s

fib : Stream Nat
head      fib = Z
head tail fib = S Z
tail tail fib = zipWith (+) fib (tail fib)

mutual
  evens : Stream a -> Stream a
  head (evens s) = head s
  tail (evens s) = odds (tail s)

  odds : Stream a -> Stream a
  odds s = evens (tail s)

merge : Stream Nat -> Stream Nat
head (merge s t) = if (head s) <= (head t) then head s else head t
tail (merge s t) = if (head s) <= (head t) then
                      if (head t <= head s) then
                        merge (tail s) (tail t)
                      else
                        merge (tail s) t
                   else
                     merge s (tail t)

hamming : Stream Nat
head hamming = 1
tail hamming = 
  (merge (map (\x -> 2 * x) hamming)
  (merge (map (\x -> 3 * x) hamming)
         (map (\x -> 5 * x) hamming)))

-- Binary Trees
codata BinTree : Type -> Type where
  value : BinTree a -> a
  left  : BinTree a -> BinTree a
  right : BinTree a -> BinTree a
  constructor _|_|_

map : (a -> b) -> BinTree a -> BinTree b
value f t = f (value t)
left  f t = map f (left t)
right f t = map f (right t)

fact : Nat -> Nat
fact Z   = S Z
fact S n = (S n) * (fact n)

-- This lacks a proof that we are not dividing by 0
choose : Nat -> Nat -> Nat
choose n k = (fact n) / ((fact k) * fact (n - k))

pascal : BinTree Nat
pascal = pascal' Z Z
  where pascal' : Nat -> Nat -> BinTree Nat
        value (pascal' n k) = choose n k
        left  (pascal' n k) = pascal' (S n)    k
        right (pascal' n k) = pascal' (S n) (S k)
