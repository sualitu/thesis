module GuardedRecursion

%default total

data Later : Type -> Type where
  next  : a -> Later a

compose : Later (a -> b) -> Later a -> Later b
compose (next t) (next u) = next (t u)  
  
instance Functor Later where
  map f (next t) = next (f t)
  
instance Applicative Later where
  pure = next
  (next t) <$> (next u) = compose (next t) (next u) 
{-
data Box : Type where
  Boxed   : Box
  Unboxed : Box
                                                      
data GT : Box -> Type -> Type where
  Guard : (b : Box) -> a -> GT b a

instance Functor (GT b) where
  map f g = case g of 
              Guard b a => Guard b (f a)
-}

partial
fix : (Later a -> a) -> a
fix f = f (next (fix f))

nextid : (u : Later a) -> ((next id) <$> u) = u
nextid (next x) = Refl

nextcompose : (s : Later (b -> c)) -> (t : Later (c -> b)) -> (u : Later c) -> ((next (.) <$> s) <$> t) <$> u = s <$> (t <$> u) 
nextcompose (next s') (next t') (next u') = Refl

nextcompose' : (t : (a -> b)) -> (u : a) -> next t <$> next u = next (t u)
nextcompose' t' u' = Refl

nextright : (u : Later (a -> b)) -> (t : a) -> u <$> next t =  next(\g => g t) <$> u
nextright (next u') t = Refl

laterDist : Later (Later (a -> b)) -> Later (Later a -> Later b)
laterDist (next t) = next (t <$>)

nLater : Nat -> Type -> Type
nLater Z a = a
nLater (S n) a = Later (nLater n a)

nCompose : (n : Nat) -> nLater (S n) (a -> b) -> nLater (S n) a -> nLater (S n) b
nCompose Z t u = compose t u
nCompose (S n') (next t) (next u) = next (nCompose n' t u)

doubleCompose : Later (Later (a -> b)) -> Later (Later a) -> Later (Later b)
doubleCompose = nCompose 1

oneComposeIsCompose : (nCompose 0 t u) = compose t u
oneComposeIsCompose = Refl

twoComposeIsDoubleCompose : (nCompose 1 t u) = doubleCompose t u
twoComposeIsDoubleCompose = Refl

unsafeForce : Later a -> a
unsafeForce (next t) = t

app1 : Later (a -> b) -> a -> Later b
app1 f a = f <$> (next a)

app1' : nLater (S n) (a -> b) -> nLater n a -> nLater (S n) b
app1' {n} f a = nCompose n f (next a)

app1n : (n : Nat) -> nLater n (a -> b) -> a -> nLater n b
app1n (S Z) f a = f <$> (next a)
app1n (S n') (next f) a = next $ (app1n n' f a)

app1Eq : app1 f a = app1n 1 f a
app1Eq = Refl

app1Eq' : app1n 1 (next f) a = app1' {n = Z} (next f) a
app1Eq' = Refl

app2 : (a -> b) -> Later a -> Later b
app2 f (next a) = next (f a)

app2' : nLater n (a -> b) -> nLater (S n) a -> nLater (S n) b
app2' {n} f a = nCompose n (next f) a

app2n : (n : Nat) -> (a -> b) -> nLater n a -> nLater n b
app2n Z f a = f a
app2n (S Z) f (next a) = next (f a)
app2n (S n') f (next a) = next (app2n n' f a)

app2Eq : (eq : (next b) = a) -> app2 f a = app2n 1 f a
app2Eq = ?app2EqMeta

app2Eq' : (eq : (next b) = a) -> app2n 1 f a = app2' {n = Z} f a
app2Eq' = ?app2Eq'Meta

app3 : (a -> b) -> a -> Later b
app3 f a = next (f a)

app3' : nLater n (a -> b) -> nLater n a -> nLater (S n) b
app3' {n} f a = nCompose n (next f) (next a)

app3n : (n : Nat) -> (a -> b) -> a -> nLater n b
app3n Z f a = f a
app3n (S n') f a = next (app3n n' f a)

app4 : Later (a -> b) -> Later a -> Later b
app4 = nCompose 0

app4' : nLater (S n) (a -> b) -> nLater (S n) a -> nLater (S n) b
app4' {n} = nCompose n

app4n : (n : Nat) -> nLater (S n) (a -> b) -> nLater (S n) a -> nLater (S n) b
app4n n = app4' {n}

corecord Stream' : Type -> Type where
   hd : Stream' a -> a
   tl : Stream' a -> Later (Stream' a)
   constructor StreamCons
  
take' : (n : Nat) -> Stream' a -> Vect n a
take' Z _ = []
take' (S n) s = (hd s) :: (take' n (unsafeForce (tl s)))

partial
take'' : (n : Nat) -> Stream' a -> List a
take'' = fix(\t,n,s => case n of
                         Z    => []
                         S n' => (hd s) :: (unsafeForce ( ( t <$> (next n') ) <$> (tl s))))

partial
zeros : Stream' Nat
zeros = fix (\f => StreamCons 0 f)

partial
moreZeros : Stream' Nat
moreZeros = fix (\f => StreamCons 0 (app1 (app3 StreamCons 0) f))

partial
prepend : List a -> Stream' a -> Stream' a
prepend = fix (\p => \l => \s => case l of
                                   [] => s
                                   (x :: xs) => StreamCons x ((p <$> (next xs)) <$> (next s)))

{-
partial
prepend'Z : Vect Z a -> Stream' a -> Stream' a
prepend'Z = fix (\p, [], s => s)

prepend'S : Vect (S n) a -> Stream' a -> Stream' a
prepend'S = fix (\p, (x :: xs), s => StreamCons x (p <$> (next xs) <$> (next s)))
-}
partial
hMerge : Stream' a -> Stream' a -> Stream' a
hMerge = fix (\m => \xs => \ys => StreamCons (hd xs) (next (StreamCons (hd ys) (m <$> (tl xs) <$> (tl ys)))))

partial
hMerge' : Stream' a -> Stream' a -> Stream' a
hMerge' = fix (\m => \xs => \ys => StreamCons (hd xs) ((next StreamCons <$> next (hd ys)) <$> next ((m <$> (tl xs)) <$> (tl ys))))

partial
mergef : (a -> a -> Later (Stream' a) -> Stream' a) -> Stream' a -> Stream' a -> Stream' a
mergef f = fix (\m => \xs => \ys => f (hd xs) (hd ys) ((m <$> (tl xs)) <$> (tl ys)))

partial
mergef' : (a -> a -> Later (Stream' a) -> Stream' a) -> Stream' a -> Stream' a -> Stream' a
mergef' = fix (\m => \f => \xs => \ys => f (hd xs) (hd ys) (((m <$> (next f)) <$> (tl xs)) <$> (tl ys)))
{-
unguard : (GT Boxed a) -> a
unguard (Guard _ a) = a

partial
gMap : (a -> b) -> (GT x (Stream' a)) -> (GT x (Stream' b))
gMap = fix (\m, f, s => Guard x (StreamCons (map (f . hd) s)  ))

partial
gEven : (GT Boxed (Stream' a)) -> (GT Boxed (Stream' a))
-}
partial
sMap : (a -> b) -> Stream' a -> Stream' b
sMap = fix (\m => \f => \s => StreamCons (f (hd s)) ((m <$> (next f)) <$> (tl s)))

partial
sMap' : (a -> b) -> Stream' a -> Stream' b
sMap' = fix (\m => \f => \s => StreamCons (f (hd s)) (app4 (app1 m f) (tl s)))

partial
sMerge : Ord a => Stream' a -> Stream' a -> Stream' a
sMerge = fix (\m => \s => \t => StreamCons 
                                 (if (hd s) <= (hd t) then hd s else hd t) 
                                 (if (hd s) <= (hd t) then              
                                     (if (hd t <= hd s) then
                                        app4 (app4 m (tl s)) (tl t)
                                     else
                                        app1 (app4 m (tl s)) t)
                                 else
                                    app4 (app1 m s) (tl t)))

partial
hamming : Stream' Nat
hamming = fix (\h => StreamCons 1
		            (((next sMerge) <$> ((next (sMap (\x => 2 * x)) <$> h))) <$>
                                               (((next sMerge) <$> (next (sMap (\x => 3 * x)) <$> h)) <$>
                                                                   (next (sMap (\x => 5 * x)) <$> h))))

partial
zipWith' : (a -> b -> c) -> Stream' a -> Stream' b -> Stream' c
zipWith' f = fix(\g => \s => \t => StreamCons (f (hd s) (hd t)) (g <$> (tl s) <$> (tl t)))

partial
zipWithNat : (Nat -> Nat -> Nat) -> Stream' Nat -> Stream' Nat -> Stream' Nat
zipWithNat = zipWith' {a=Nat} {b=Nat} {c=Nat}

partial
fib : Stream' Nat
fib = fix (\f => StreamCons 0 (app4 (app3 StreamCons 1) (app4' (app1' {n=1} (app3n 2 zipWithNat (+)) f) (app2 tl f))))

partial
nats : Stream' Nat
nats = fix (\n => StreamCons 0 ((next sMap <$> next S) <$> n))


partial tailtail : Stream' a -> Later (Later (Stream' a))
tailtail = fix(\t, s => (next tl) <$> (tl s))

hat : nLater (S n) (a -> b) -> (Later (nLater n a -> nLater n b))
hat = ?h

partial nats2 : Stream' Nat
nats2 = fix(\n => StreamCons 0 (app4 (app3 StreamCons 1) (app4 (hat {n=1} (app3n 2 sMap S)) (app2 tl n))))

partial bad : (Stream' Nat)
bad = fix(\b => b)

corecord Foo : Type where
  bar : Foo -> Bool
  baz : (f : Foo) -> (if bar f then (Later Foo) else Nat)
  
partial
alpha : Foo
alpha = fix (\a => MkFoo True (next alpha))


---------- Proofs ----------

GuardedRecursion.app2EqMeta = proof
  intros
  rewrite eq
  compute
  refine Refl

GuardedRecursion.app2Eq'Meta = proof
  intros
  rewrite eq
  compute
  refine Refl

