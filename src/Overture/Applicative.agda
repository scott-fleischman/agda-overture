module Overture.Applicative where

open import Agda.Primitive
open import Overture.Functor

record Applicative
  {lx ly : Level}
  {T : Set lx → Set ly}
  (F : Functor T)
  : Set (lsuc lx ⊔ ly)
  where
  constructor makeApplicative
  field
    pure
      : {A : Set lx}
      → A
      → T A

    apply
      : {A B : Set lx}
      → T (A → B)
      → T A
      → T B
