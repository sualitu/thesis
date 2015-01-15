module Fractions

%default total

record Fraction : Type where
  F : (top : Nat) -> (bottom : Nat) -> Fraction
  
codata Tree : Type -> Type where
  MkTree : a -> Tree a -> Tree a -> Tree a
  
fracSum : Fraction -> Nat
fracSum (F top bottom) = top + bottom

leftFrac : Fraction -> Fraction
leftFrac f = F (top f) (fracSum f)

rightFrac : Fraction -> Fraction
rightFrac f = F (fracSum f) (bottom f)
  
flattenTree : Tree a -> Stream a
flattenTree t = ft [t]
  where
    %assert_total  
    ft : List (Tree a) -> Stream a
    ft ((MkTree v l r) :: xs) = v :: (ft (xs ++ [l, r]))

rationalTree : Tree Fraction
rationalTree = rt (F 1 1)
  where
    rt : Fraction -> Tree Fraction
    rt f = MkTree f (rt (leftFrac f)) (rt (rightFrac f))

rationals : Stream Fraction
rationals = flattenTree $ rationalTree
