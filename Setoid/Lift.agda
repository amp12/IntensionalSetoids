module Setoid.Lift where

open import Prelude

open import Setoid.Definition
open import Setoid.Universes

----------------------------------------------------------------------
-- Lifting from a universe to a higher one
----------------------------------------------------------------------
Ins :
  {m n : ℕ}
  (_ : n ≥ m)
  → ---------------
  Setd[ 𝒰 m ⟶ 𝒰 n ]

∣ Ins ≥refl ∣ = id
∣ Ins (≥step p) ∣ = In ∘ ∣ Ins p ∣
cng (Ins ≥refl) _ _ e = e
cng (Ins (≥step p)) = cng (Ins p)

Insℰ𝓁 :
  {m n : ℕ}
  (p : n ≥ m)
  → -----------------
  ℰ𝓁 m ≡ ℰ𝓁 n * Ins p

Insℰ𝓁 ≥refl = refl
Insℰ𝓁 (≥step p) = Insℰ𝓁 p

InsInj :
  {m n : ℕ}
  (p : n ≥ m)
  {A B : U m}
  (_ : 𝒰 n ∋ ∣ Ins p ∣ A ~ ∣ Ins p ∣ B)
  → -----------------------------------
  𝒰 m ∋ A ~ B

InsInj ≥refl e = e
InsInj (≥step p) e = InsInj p e
