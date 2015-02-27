module CoinductionExamples

%default total

data Nat = Z | S Nat

%case data Bool = False | True

||| The underlying implementation of the if ... then ... else ... syntax
||| @ b the condition on the if
||| @ t the value if b is true
||| @ e the falue if b is false
boolElim : (b : Bool) -> (t : Lazy a) -> (e : Lazy a) -> a
boolElim True  t e = t
boolElim False t e = e

-- Syntactic sugar for boolean elimination.
syntax if [test] then [t] else [e] = boolElim test (Delay t) (Delay e)

infixr 10 +
infixr 10 -
infixr 10 ::
infixr 10 ==

(==) : Nat -> Nat -> Bool
Z == Z = True
(S n) == (S m) = n == m
_ == _ = False

(+) : Nat -> Nat -> Nat
(+) n Z = n
(+) n (S m) = S (n + m)

(-) : Nat -> Nat -> Nat
(-) n Z = n
(-) (S n) (S m) = n - m
(-) Z _ = Z

mult : Nat -> Nat -> Nat
mult Z right        = Z
mult (S left) right = right + (mult left right)

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

total causal fib : Stream Nat
&head fib = Z
&head &tail fib = S Z
&tail &tail fib = zipWith (+) fib (tail fib)

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

total causal toggle : Stream Nat
&head toggle = Z
&head &tail toggle = S Z
&tail &tail toggle = toggle

total causal paperfold : Stream Nat
&head paperfold = Z
&tail paperfold = interleave paperfold toggle

total causal paperfold' : Stream Nat
paperfold' = interleave toggle paperfold'

total causal cycle : Nat -> Stream Nat
cycle n = cycle' n n
  where
    total causal cycle' : Nat -> Nat -> Stream Nat
    &head cycle' Z     m = Z
    &head cycle' (S n) m = (S n)
    &tail cycle' Z     m = cycle' m m
    &tail cycle' (S n) m = cycle' n m
    
total causal fac : Stream Nat
fac = (S Z) :: (zipWith mult (map S nats) fac)

total causal mergef : (Nat -> Nat -> Stream Nat -> Stream Nat) -> Stream Nat -> Stream Nat -> Stream Nat
mergef f s t = f (head s) (head t) (mergef f (tail s) (tail t))

namespace List
  data List : Type -> Type where
    nil : List a
    (::) : a -> List a -> List a

  total causal prepend : List a -> Stream a -> Stream a
  prepend [] s = s
  prepend (x ::xs) s = x :: (prepend xs s)
  
infixr 10 <=

(<=) : Nat -> Nat -> Bool
(<=) Z _ = True
(<=) (S n) Z = False
(<=) (S n) (S m) = n <= m


total causal merge : Stream Nat -> Stream Nat -> Stream Nat
&head merge s t = case (head s <= head t) of
                    True  => (head s) 
                    False => (head t)
&tail merge s t = case (head s <= head t) of
                    True  => case (head t <= head s) of
                               True  => (merge (tail s) (tail t))
                               False => (merge (tail s) t)
                    False => (merge s (tail t))

corecord Tree : Type -> Type where
  value : Tree a -> a
  left  : Tree a -> Tree a
  right : Tree a -> Tree a
       
total causal tmap : (a -> b) -> Tree a -> Tree b
&value tmap f t = f (value t)
&left  tmap f t = tmap f (left  t)
&right tmap f t = tmap f (right t)

total causal tzip : (a -> b -> c) -> Tree a -> Tree b -> Tree c
&value tzip f t r = f (value t) (value r)
&left  tzip f t r = tzip f (left  t) (left  r)
&right tzip f t r = tzip f (right t) (right r)

total causal trepeat : a -> Tree a
&value trepeat n = n
&left  trepeat n = trepeat n
&right trepeat n = trepeat n

total causal carry : Tree Nat
&value carry = S Z
&left  carry = trepeat Z
&right carry = tmap S carry

fst' : (a, b, c) -> a
fst' (x, _, _) = x

snd' : (a, b, c) -> b
snd' (_, y, _) = y

trd' : (a, b, c) -> c
trd' (_, _, z) = z

total causal unfoldTree : (s -> (a, s, s)) -> s -> Tree a
&value unfoldTree step x = fst' (step x)
&left  unfoldTree step x = unfoldTree step (snd' (step x))
&right unfoldTree step x = unfoldTree step (trd' (step x))

total causal calculateWilfully : Tree (Nat, Nat)
calculateWilfully = grow((S Z), (S Z))
  where
    total causal grow : (Nat, Nat) -> Tree(Nat, Nat)
    grow (n, d) = MkTree (n, d) (grow(n, n + d)) (grow(n + d, d))
  
data Either a b = Left a | Right b  

corecord Partiality : Type -> Type where
  p : Partiality a -> Either a (Partiality a)
  constructor P
  
total causal never : Partiality a
never = P (Right never)

total causal bind : Partiality a -> (a -> Partiality b) -> Partiality b
bind (P (Left x)) f = f x
bind (P (Right x)) f = P (Right (bind x f))

corecord FunMachine : Type -> Type where
  skip : FunMachine a -> FunMachine a
  calc : FunMachine a -> (a, FunMachine a)
  fun : FunMachine a -> (a -> a)
  
total causal multmachine : Stream Nat -> FunMachine Nat
&skip multmachine s = multmachine (tail s)
&calc multmachine s = ((fun (multmachine $ tail s) (head s)), (multmachine $ tail s))
&fun multmachine s = mult (head s)

data Response = OK | BadRequest

reject : a -> Response
reject _ = BadRequest

total causal pingserver : FunMachine Response
&skip pingserver = pingserver
&calc pingserver = (OK, pingserver)
&fun  pingserver = reject

ping : Response
ping = fst (calc pingserver)

corecord Idler : Type -> Type where
  idle : Idler a -> Idler a
  stop : Idler a -> a
  
total causal pingserver' : Idler Response
&idle pingserver' = pingserver'
&stop pingserver' = OK

ping' : Response
ping' = stop (idle (idle pingserver'))

causal imap : (a -> b) -> Idler a -> Idler b
&idle imap f i = imap f (idle i)
&stop imap f i = f (stop i)

total causal counter : Nat -> Idler Nat
&idle counter n = imap S (counter n) 
&stop counter n = n
