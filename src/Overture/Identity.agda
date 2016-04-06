module Overture.Identity where

open import Agda.Primitive

id
  : {la : Level}
  → {A : Set la}
  → A
  → A
id a = a
