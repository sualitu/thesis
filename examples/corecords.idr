module Corecords

-- Standard Streams

corecord Stream' : Type -> Type where
  hd : Stream' a -> a
  tl : Stream' a -> Stream' a
  constructor MkStream' (hd tl)
  
record Foo : Type -> Type where
  MkFoo : (bar : a) -> (baz : Foo a) -> Foo a
  
-- Bisimilarity for streams
-- Thanks to asal@itu.dk
-- Ahmad Salim Al-Sibahi

{- 
Does not work.

corecord BisimStream' : Stream' a -> Stream' a -> Type where
  phd : BisimStream' s s' -> (hd s) = (hd s')
  ptl : BisimStream' s s' -> BisimStream' (tl s) (tl s')
-}

corecord BisimStream' : (a : Type) -> Stream' a -> Stream' a -> Type where
  phd : BisimStream' a s s' -> (hd s) = (hd s')
  ptl : BisimStream' a s s' -> BisimStream' a (tl s) (tl s')

-- CoTree

corecord CoTree : Type -> Type where
  value : CoTree a -> a
  left  : CoTree a -> CoTree a
  right : CoTree a -> CoTree a

-- Globular types    
-- https://code.google.com/p/agda/issues/detail?id=906

corecord Glob : Type where
  Ob : Glob -> Type
  Hom : Glob -> Glob -> Glob -> Glob
    
Unit_glob : Glob 
Unit_glob = MkGlob Unit (\_, _ => Unit_glob)

Id_glob : Type -> Glob
Id_glob a = MkGlob a (\a, b => Id_glob (a = b))

-- Dependent Projections
{-
corecord Foo : Type where
  bar : Foo -> Bool
  baz : (f : Foo) -> if bar f then Nat else Bool -> Foo
  constructor MkFoo (bar baz)-}
