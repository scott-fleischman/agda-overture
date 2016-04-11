module Overture.Maybe where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Overture.Identity
open import Overture.Composition
open import Overture.Function
open import Overture.Functor
open import Overture.FunctorLaws
open import Overture.Applicative
open import Overture.ApplicativeLaws

data Maybe
  {la : Level}
  (A : Set la)
  : Set la
  where
  some : A → Maybe A
  none : Maybe A

module MaybeFunctor where
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
functor = record { MaybeFunctor }

module MaybeFunctorLaws where
  open MaybeFunctor

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
functorLaws = record { MaybeFunctorLaws }

module MaybeApplicative where
  pure
    : {lx : Level}
    → {A : Set lx}
    → A
    → Maybe A
  pure a = some a

  apply
    : {lx : Level}
    → {A B : Set lx}
    → Maybe (A → B)
    → Maybe A
    → Maybe B
  apply (some f) (some a) = some (f a)
  apply none (some a) = none
  apply _ none = none

applicative
  : {lx : Level}
  → Applicative {lx = lx} functor
applicative = record { MaybeApplicative }

module MaybeApplicativeLaws where
  open MaybeApplicative

  identity
    : {lx : Level}
    → {A : Set lx}
    → (ta : Maybe A)
    → apply (pure id) ta ≡ ta
  identity (some a) = refl
  identity none = refl

  composition
    : {lx : Level}
    → {A B C : Set lx}
    → (tg : Maybe (B → C))
    → (tf : Maybe (A → B))
    → (ta : Maybe A)
    → apply (apply (apply (pure cmp) tg) tf) ta ≡ apply tg (apply tf ta)
  composition (some g) (some f) (some a) = refl
  composition (some g) (some f) none = refl
  composition (some g) none (some a) = refl
  composition (some g) none none = refl
  composition none (some f) (some a) = refl
  composition none (some f) none = refl
  composition none none (some a) = refl
  composition none none none = refl

  homomorphism
    : {lx : Level}
    → {A B : Set lx}
    → (f : A → B)
    → (a : A)
    → apply (pure f) (pure a) ≡ pure (f a)
  homomorphism f a = refl

  interchange
    : {lx : Level}
    → {A B : Set lx}
    → (f : Maybe (A → B))
    → (a : A)
    → apply f (pure a) ≡ apply (pure (ap a)) f
  interchange (some f) a = refl
  interchange none a = refl

applicativeLaws
  : {lx : Level}
  → ApplicativeLaws {lx = lx} applicative
applicativeLaws = record { MaybeApplicativeLaws }
