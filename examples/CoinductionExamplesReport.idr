module Coinduction

corecord Stream a where
  head : a
  tail : Stream a
  
total causal 
zeros : Stream Nat
&head zeros = Z
&tail zeros = zeros

total causal 
repeat : a -> Stream a
&head repeat n = n
&tail repeat n = repeat n

total causal 
map : (a -> b) -> Stream a -> Stream b
&head map f s = f (head s)
&tail map f s = map f (tail s)

total causal 
nats : Stream Nat
&head nats = Z
&tail nats = map S nats

total causal 
zipWith : (a -> b -> c) -> Stream a -> Stream b -> Stream c
&head zipWith f s t = f (head s) (head t)
&tail zipWith f s t = zipWith f (tail s) (tail t)

total causal 
fib : Stream Nat
&head       fib = Z
&head &tail fib = S Z
&tail &tail fib = zipWith (+) fib (tail fib)

total causal 
unfold : (s -> (a, s)) -> s -> Stream a
&head unfold step x = fst (step x)
&tail unfold step x = unfold step (snd (step x))

total causal 
interleave : Stream a -> Stream a -> Stream a
&head interleave s t = head s
&tail interleave s t = interleave t (tail s)

total causal 
toggle : Stream Nat
&head       toggle = Z
&head &tail toggle = S Z
&tail &tail toggle = toggle

total causal 
paperfold : Stream Nat
&head paperfold = Z
&tail paperfold = interleave paperfold toggle

total causal 
paperfold' : Stream Nat
paperfold' = interleave toggle paperfold'

total causal 
cycle : Nat -> Stream Nat
cycle n = cycle' n n
  where
    total causal 
    cycle' : Nat -> Nat -> Stream Nat
    &head cycle' Z     m = Z
    &head cycle' (S n) m = (S n)
    &tail cycle' Z     m = cycle' m m
    &tail cycle' (S n) m = cycle' n m
    
total causal 
fac : Stream Nat
&head fac = (S Z)
&tail fac = (zipWith (*) (map S nats) fac)

total causal 
mergef : (Nat -> Nat -> Stream Nat -> Stream Nat) -> 
              Stream Nat -> Stream Nat -> Stream Nat
mergef f s t = f (head s) (head t) (mergef f (tail s) (tail t))

total causal
prepend : List a -> Stream a -> Stream 
prepend []       s = s
prepend (x ::xs) s = x :: (prepend xs s)

corecord Tree : Type -> Type where
  value : Tree a -> a
  left  : Tree a -> Tree a
  right : Tree a -> Tree a
       
total causal 
tmap : (a -> b) -> Tree a -> Tree b
&value tmap f t = f (value t)
&left  tmap f t = tmap f (left  t)
&right tmap f t = tmap f (right t)

total causal 
tzip : (a -> b -> c) -> Tree a -> Tree b -> Tree c
&value tzip f t r = f (value t) (value r)
&left  tzip f t r = tzip f (left  t) (left  r)
&right tzip f t r = tzip f (right t) (right r)

total causal 
trepeat : a -> Tree a
&value trepeat n = n
&left  trepeat n = trepeat n
&right trepeat n = trepeat n

total causal 
carry : Tree Nat
&value carry = S Z
&left  carry = trepeat Z
&right carry = tmap S carry

total causal unfoldTree : (s -> (a, s, s)) -> s -> Tree a
&value unfoldTree step x = fst' (step x)
&left  unfoldTree step x = unfoldTree step (snd' (step x))
&right unfoldTree step x = unfoldTree step (trd' (step x))




total causal 
calculateWilfully : Tree (Nat, Nat)
calculateWilfully = grow((S Z), (S Z))
  where
    total causal 
    grow : (Nat, Nat) -> Tree(Nat, Nat)
    grow (n, d) = MkTree (n, d) (grow(n, n + d)) (grow(n + d, d))

corecord Partiality : Type -> Type where
  p : Partiality a -> Either a (Partiality a)
  constructor P
  
total causal 
never : Partiality a
never = P (Right never)

total causal 
bind : Partiality a -> (a -> Partiality b) -> Partiality b
bind (P (Left x)) f = f x
bind (P (Right x)) f = P (Right (bind x f))

corecord FunMachine : Type -> Type where
  skip : FunMachine a -> FunMachine a
  calc : FunMachine a -> (a, FunMachine a)
  fun  : FunMachine a -> (a -> a)
  
total causal 
multmachine : Stream Nat -> FunMachine Nat
&skip multmachine s = multmachine (tail s)
&calc multmachine s = 
     (fun (multmachine $ tail s) (head s) , 
      multmachine $ tail s)
&fun  multmachine s = (*) (head s)

data Response = OK | BadRequest

total
reject : a -> Response
reject _ = BadRequest

total causal 
pingserver : FunMachine Response
&skip pingserver = pingserver
&calc pingserver = (OK, pingserver)
&fun  pingserver = reject


corecord Idler : Type -> Type where
  idle : Idler a -> Idler a
  stop : Idler a -> a
  
total causal 
pingserver' : Idler Response
&idle pingserver' = pingserver'
&stop pingserver' = OK

ping' : Response
ping' = stop (idle (idle pingserver'))

total causal 
imap : (a -> b) -> Idler a -> Idler b
&idle imap f i = imap f (idle i)
&stop imap f i = f (stop i)

total causal 
counter : Nat -> Idler Nat
&idle counter n = imap S (counter n) 
&stop counter n = n
