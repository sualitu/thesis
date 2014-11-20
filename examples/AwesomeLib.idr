module AwesomeLib

data Awesome : Type -> Type where
  MkAwesome : a -> Awesome a
