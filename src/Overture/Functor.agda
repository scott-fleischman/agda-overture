module Overture.Functor where

open import Agda.Primitive

record Functor
  {lx ly : Level}
  (F : Set lx → Set ly)
  : Set (lsuc lx ⊔ ly)
  where
  field
    map
      : {A B : Set lx}
      → (A → B)
      → F A
      → F B
