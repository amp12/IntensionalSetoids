module Setoid.EmptyType where

open import Prelude

open import Setoid.Definition
open import Setoid.Display
open import Setoid.Universes
open import Setoid.Lift

----------------------------------------------------------------------
-- Empty type
----------------------------------------------------------------------
emp :
  (l : ℕ)
  (X : U l)
  (e : El 0 Emp)
  → ------------
  El l X

emp _ _ ()

empCong :
  {l : ℕ}
  {X X' : U l}
  {e e' : El 0 Emp}
  (_ : 𝒰 l ∋ X ~ X')
  (_ : ℰ𝓁 0 ∋ Emp , e ≈ Emp , e')
  → --------------------------------------
  ℰ𝓁 l ∋ X , emp l X e  ≈ X' , emp l X' e'

empCong {e = ()} _ _
