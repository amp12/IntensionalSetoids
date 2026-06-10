module Prelude.Sum where

open import Prelude.Level

----------------------------------------------------------------------
-- Disjoint union
----------------------------------------------------------------------
infixr 6 _⊎_
data _⊎_ {l m : Level}(A : Set l)(B : Set m) : Set (l ⊔ m) where
  ι₁ : (x : A) → A ⊎ B
  ι₂ : (y : B) → A ⊎ B

----------------------------------------------------------------------
-- Disjunction
----------------------------------------------------------------------
infixr 2 _∨_

_∨_ : {l m : Level}(A : Set l)(B : Set m) → Set (l ⊔ m)
_∨_ = _⊎_

∨elim :
  {l m n : Level}
  {A : Set l}
  {B : Set m}
  {C : Set n}
  (_ : A → C)
  (_ : B → C)
  → -------------
  A ∨ B → C

∨elim f g (ι₁ x) = f x
∨elim f g (ι₂ y) = g y
