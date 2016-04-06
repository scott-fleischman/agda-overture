module Overture.Maybe where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Overture.Identity
open import Overture.Composition
open import Overture.Functor
open import Overture.FunctorLaws

data Maybe
  {la : Level}
  (A : Set la)
  : Set la
  where
  some : A → Maybe A
  none : Maybe A

map
  : {lx : Level}
  → {A B : Set lx}
  → (A → B)
  → Maybe A
  → Maybe B
map f (some x) = some (f x)
map f none = none

functor
  : {lx : Level}
  → Functor {lx = lx} Maybe
functor = record { map = map }

identity
  : {lx : Level}
  → {A : Set lx}
  → (x : Maybe A)
  → map id x ≡ id x
identity (some x) = refl
identity none = refl

composition
  : {lx : Level}
  → {A B C : Set lx}
  → (g : B → C)
  → (f : A → B)
  → (x : Maybe A)
  → map (g ∘ f) x ≡ (map g ∘ map f) x
composition g f (some x) = refl
composition g f none = refl

functorLaws
  : {lx : Level}
  → FunctorLaws {lx = lx} functor
functorLaws = record { identity = identity ; composition = composition }
