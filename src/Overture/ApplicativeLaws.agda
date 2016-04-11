module Overture.ApplicativeLaws where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Overture.Identity
open import Overture.Composition
open import Overture.Functor
open import Overture.Applicative

open Applicative

record ApplicativeLaws
  {lx ly : Level}
  {T : Set lx → Set ly}
  {F : Functor T}
  (AP : Applicative F)
  : Set (lsuc lx ⊔ ly)
  where
  constructor makeApplicativeLaws
  field
    identity
      : {A : Set lx}
      → (x : T A)
      → apply AP (pure AP id) x ≡ x

    homomorphism
      : {A B : Set lx}
      → (f : A → B)
      → (x : A)
      → apply AP (pure AP f) (pure AP x) ≡ pure AP (f x)

    interchange
      : {A B : Set lx}
      → (f : T (A → B))
      → (x : A)
      → apply AP f (pure AP x) ≡ apply AP (pure AP (λ g → g x)) f
