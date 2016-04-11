module Overture.List where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Overture.Identity
open import Overture.Composition
open import Overture.Function
open import Overture.Functor
open import Overture.FunctorLaws
open import Overture.Applicative
open import Overture.ApplicativeLaws

data List
  {la : Level}
  (A : Set la)
  : Set la
  where
  [] : List A
  _∷_ : A → List A → List A

append
  : {lx : Level}
  → {A : Set lx}
  → List A
  → List A
  → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ (append xs ys)

module ListFunctor where
  map
    : {lx : Level}
    → {A B : Set lx}
    → (A → B)
    → List A
    → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

functor
  : {lx : Level}
  → Functor {lx = lx} List
functor = record { ListFunctor }

module ListFunctorLaws where
  open ListFunctor

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

functorLaws
  : {lx : Level}
  → FunctorLaws {lx = lx} functor
functorLaws = record { ListFunctorLaws }

module ListApplicative where
  open ListFunctor

  pure
    : {lx : Level}
    → {A : Set lx}
    → A
    → List A
  pure a = a ∷ []

  apply
    : {lx : Level}
    → {A B : Set lx}
    → List (A → B)
    → List A
    → List B
  apply [] xs = []
  apply {lx = lx} (f ∷ fs) xs = append (map f xs) (apply fs xs)

applicative
  : {lx : Level}
  → Applicative {lx = lx} functor
applicative = record { ListApplicative }

module ListApplicativeLaws where
  open ListApplicative
  open ListFunctor

  appendEmptyRight
    : {lx : Level}
    → {A : Set lx}
    → (xs : List A)
    → append xs [] ≡ xs
  appendEmptyRight [] = refl
  appendEmptyRight (x ∷ xs) rewrite appendEmptyRight xs = refl

  applyEmptyRight
    : {lx : Level}
    → {A B : Set lx}
    → (xs : List (A → B))
    → apply xs [] ≡ []
  applyEmptyRight [] = refl
  applyEmptyRight (x ∷ xs) rewrite applyEmptyRight xs = refl

  identity
    : {lx : Level}
    → {A : Set lx}
    → (x : List A)
    → apply (pure id) x ≡ x
  identity [] = refl
  identity (x ∷ xs) rewrite ListFunctorLaws.identity xs | appendEmptyRight xs = refl

  composition
    : {lx : Level}
    → {A B C : Set lx}
    → (tg : List (B → C))
    → (tf : List (A → B))
    → (ta : List A)
    → apply (apply (apply (pure cmp) tg) tf) ta ≡ apply tg (apply tf ta)
  composition [] tf ta = refl
  composition {A = A} (g ∷ tg) [] ta
    rewrite applyEmptyRight tg
    | applyEmptyRight (apply (pure (cmp {A = A})) tg)
    = refl
  composition {A = A} (g ∷ tg) (f ∷ tf) []
    rewrite applyEmptyRight tf
    | applyEmptyRight tg
    | appendEmptyRight (map (cmp {A = A}) tg)
    | applyEmptyRight (append (map (cmp g) tf) (apply (map cmp tg) (f ∷ tf)))
    = refl
  composition (g ∷ tg) (f ∷ tf) (a ∷ ta) = {!!}

  homomorphism
    : {lx : Level}
    → {A B : Set lx}
    → (f : A → B)
    → (x : A)
    → apply (pure f) (pure x) ≡ pure (f x)
  homomorphism f x = refl

  interchange
    : {lx : Level}
    → {A B : Set lx}
    → (f : List (A → B))
    → (x : A)
    → apply f (pure x) ≡ apply (pure (ap x)) f
  interchange [] x = refl
  interchange (f ∷ fs) x rewrite interchange fs x = refl

applicativeLaws
  : {lx : Level}
  → ApplicativeLaws {lx = lx} applicative
applicativeLaws = record { ListApplicativeLaws }
