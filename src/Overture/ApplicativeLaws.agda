module Overture.ApplicativeLaws where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Overture.Identity
open import Overture.Composition
open import Overture.Function
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
      → (ta : T A)
      → apply AP (pure AP id) ta ≡ ta

    composition
      : {A B C : Set lx}
      → (tg : T (B → C))
      → (tf : T (A → B))
      → (ta : T A)
      → apply AP (apply AP (apply AP (pure AP cmp) tg) tf) ta ≡ apply AP tg (apply AP tf ta)

    homomorphism
      : {A B : Set lx}
      → (f : A → B)
      → (a : A)
      → apply AP (pure AP f) (pure AP a) ≡ pure AP (f a)

    interchange
      : {A B : Set lx}
      → (tf : T (A → B))
      → (a : A)
      → apply AP tf (pure AP a) ≡ apply AP (pure AP (ap a)) tf
