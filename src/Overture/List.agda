module Overture.List where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Overture.Identity
open import Overture.Composition
open import Overture.Functor
open import Overture.FunctorLaws

data List
  {la : Level}
  (A : Set la)
  : Set la
  where
  [] : List A
  _∷_ : A → List A → List A

module ListFunctor where
  map
    : {lx : Level}
    → {A B : Set lx}
    → (A → B)
    → List A
    → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs
open ListFunctor

functor
  : {lx : Level}
  → Functor {lx = lx} List
functor = makeFunctor map

module ListFunctorLaws where
  identity
    : {lx : Level}
    → {A : Set lx}
    → (x : List A)
    → map id x ≡ id x
  identity [] = refl
  identity (x ∷ xs) rewrite identity xs = refl

  composition
    : {lx : Level}
    → {A B C : Set lx}
    → (g : B → C)
    → (f : A → B)
    → (x : List A)
    → map (g ∘ f) x ≡ (map g ∘ map f) x
  composition g f [] = refl
  composition g f (x ∷ xs) rewrite composition g f xs = refl
open ListFunctorLaws

functorLaws
  : {lx : Level}
  → FunctorLaws {lx = lx} functor
functorLaws = makeFunctorLaws identity composition
