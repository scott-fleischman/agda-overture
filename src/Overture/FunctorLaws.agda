module Overture.FunctorLaws where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Overture.Identity
open import Overture.Composition
open import Overture.Functor

open Functor

record FunctorLaws
  {lx ly : Level}
  {T : Set lx → Set ly}
  (F : Functor T)
  : Set (lsuc lx ⊔ ly)
  where
  field
    identity
      : {A : Set lx}
      → (x : T A)
      → map F id x ≡ id x

    composition
      : {A B C : Set lx}
      → (g : B → C)
      → (f : A → B)
      → (x : T A)
      → map F (g ∘ f) x ≡ (map F g ∘ map F f) x
