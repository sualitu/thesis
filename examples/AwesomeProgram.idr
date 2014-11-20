module AwesomeProgram

import AwesomeLib

mutual
  awesomeNat : Nat -> Awesome Nat
  awesomeNat n = MkAwesome n
