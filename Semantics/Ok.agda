module Semantics.Ok where

open import Prelude
open import Setoid
open import WSLN
open import ETT

open import Semantics.Relation

----------------------------------------------------------------------
-- The semantics of terms-in-context contains that for contexts
----------------------------------------------------------------------
ok⟦tm⟧ :
  {l : Lvl}
  {Γ : Cx}
  {a : Tm}
  {C : Uω}
  {Tt : ∑(Fam l C) (Elt l C)}
  (_ : ⟦ Γ ⊢[ l ] a tm⟧＝ (C , Tt))
  → -------------------------------
  ⟦ Γ cx⟧＝ C

ok⟦vr⟧ :
  {l : Lvl}
  {Γ : Cx}
  {x : 𝔸}
  {C : Uω}
  {Tt : ∑(Fam l C) (Elt l C)}
  (_ : ⟦ Γ ⊢[ l ] x vr⟧＝ (C , Tt))
  → -------------------------------
  ⟦ Γ cx⟧＝ C

ok⟦tm⟧ (resp⟦tm⟧ q (e , _)) = resp⟦cx⟧ (ok⟦tm⟧ q) e
ok⟦tm⟧ (⟦𝐔⟧ q) = q
ok⟦tm⟧ (⟦𝚷⟧ _ q _) = ok⟦tm⟧ q
ok⟦tm⟧ (⟦𝐄𝐪⟧ q _ _) = ok⟦tm⟧ q
ok⟦tm⟧ (⟦𝐍𝐚𝐭⟧ q) = q
ok⟦tm⟧ (⟦𝐯⟧ q) = ok⟦vr⟧ q
ok⟦tm⟧ (⟦𝛌⟧ _ q _) = ok⟦tm⟧ q
ok⟦tm⟧ (⟦∙⟧ _ q _ _ _) = ok⟦tm⟧ q
ok⟦tm⟧ (⟦𝐫𝐞𝐟𝐥⟧ q _) = ok⟦tm⟧ q
ok⟦tm⟧ (⟦𝐳𝐞𝐫𝐨⟧ q) = q
ok⟦tm⟧ (⟦𝐬𝐮𝐜𝐜⟧ q) = ok⟦tm⟧ q
ok⟦tm⟧ (⟦𝐧𝐫𝐞𝐜⟧ _ _ q _ _) = ok⟦tm⟧ q

ok⟦vr⟧ (resp⟦vr⟧ q (e , _)) = resp⟦cx⟧ (ok⟦vr⟧ q) e
ok⟦vr⟧ (⟦new⟧ q₀ q₁) = ⟦⨟⟧ q₀ q₁
ok⟦vr⟧ (⟦old⟧ q₀ _ q₂) = ⟦⨟⟧ q₀ q₂

ok⟦ty⟧ :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {C : Uω}
  {T : Fam l C}
  (_ : ⟦ Γ ⊢[ l ] A ty⟧＝ (C , T))
  → ------------------------------
  ⟦ Γ cx⟧＝ C

ok⟦ty⟧ = ok⟦tm⟧

----------------------------------------------------------------------
-- Context inversion
----------------------------------------------------------------------
⟦⨟⟧⁻¹ :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  {C : Uω}
  {T : Fam l C}
  (_ : ⟦ Γ ⨟ x ∶ A ⦂ l' cx⟧＝ (C ⋉[ l ] T))
  (_ : l' ≡ l)
  → -----------------------------------------
  (⟦ Γ ⊢[ l ] A ty⟧＝ (C , T)) ∧ (x # Γ)

⟦⨟⟧⁻¹ (⟦⨟⟧ q₀ q₁) _ = (q₀ , q₁)

----------------------------------------------------------------------
-- Membership of contexts
----------------------------------------------------------------------
⟦∈⟧→dom :
  {l : Lvl}
  {Γ : Cx}
  {x : 𝔸}
  {CTt : ∑[ C ∈ Uω ] ∑ (Fam l C) (Elt l C)}
  (_ : ⟦ Γ ⊢[ l ] x vr⟧＝ CTt)
  → ----------------------------------------
  x ∈ dom Γ

⟦∈⟧→dom (⟦new⟧ _ _) = ∈∪₂ ∈｛｝
⟦∈⟧→dom (⟦old⟧ _ q _) = ∈∪₁ (⟦∈⟧→dom q)
⟦∈⟧→dom (resp⟦vr⟧ q _) = ⟦∈⟧→dom q
