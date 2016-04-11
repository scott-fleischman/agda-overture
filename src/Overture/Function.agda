module Overture.Function where

open import Agda.Primitive

ap
  : {lx : Level}
  → {A B : Set lx}
  → A
  → (A → B)
  → B
ap a f = f a
