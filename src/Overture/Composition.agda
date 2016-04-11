module Overture.Composition where

open import Agda.Primitive

_∘_
  : {la lb lc : Level}
  → {A : Set la}
  → {B : A → Set lb}
  → {C : {a : A} → (b : B a) → Set lc}
  → (g : {a : A} → (b : B a) → C b)
  → (f : (a : A) → B a)
  → (a : A)
  → C (f a)
_∘_ g f x = g (f x)

cmp
  : {la lb lc : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → (B → C)
  → (A → B)
  → A
  → C
cmp g f x = g (f x)

cmp'
  : {lx : Level}
  → {A : Set lx}
  → {B : Set lx}
  → {C : Set lx}
  → (B → C)
  → (A → B)
  → A
  → C
cmp' g f x = g (f x)
