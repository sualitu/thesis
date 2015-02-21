module Fractions

%default total

record Fraction : Type where
  F : (top : Nat) -> (bottom : Nat) -> Fraction
  
corecord Tree : Type -> Type where
  value : Tree a -> a
  left : Tree a -> Tree a
  right : Tree a -> Tree a
  constructor MkTree
  
fracSum : Fraction -> Nat
fracSum (F top bottom) = top + bottom

leftFrac : Fraction -> Fraction
leftFrac f = F (top f) (fracSum f)

rightFrac : Fraction -> Fraction
rightFrac f = F (fracSum f) (bottom f)

total causal flattenTree : Tree a -> Stream a
flattenTree t = ft []
  where
    total causal ft : List (Tree a) -> Stream a
    ft [] = (value t) :: (ft [left t, right t])
    ft (tree :: xs) = (value tree) :: (ft (xs ++ [left tree, right tree]))
        
total causal rationalTree : Tree Fraction
rationalTree = rt $ F (S Z) (S Z)
  where
    total causal rt : Fraction -> Tree Fraction
    rt f = MkTree f (rt $ leftFrac f) (rt $ rightFrac f)

--total causal rationals : Stream Fraction
--rationals = flattenTree $ rationalTree
