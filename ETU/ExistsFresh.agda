module ETU.ExistsFresh where

open import Prelude
open import WSLN

open import ETU.Syntax
open import ETU.Judgement
open import ETU.Rules
open import ETU.Ok
open import ETU.WellScoped
open import ETU.Weakening
open import ETU.Substitution
open import ETU.Admissible

----------------------------------------------------------------------
-- "Exists fresh" style typing rules (without helper hypotheses)
----------------------------------------------------------------------
⊢𝚷⁻ :
  {Γ : Cx}
  {l l' : ℕ}
  {A : Tm}
  {B : Tm[ 1 ]}
  {x : 𝔸}
  (_ : Γ ⊢ A ⦂ l)
  (_ : (Γ ⨟ x ∶[ l ] A) ⊢ B [ x ] ⦂ l')
  (_ : x # B)
  → ----------------------------------
  Γ ⊢ 𝚷 l l' A B ⦂ (max l l')

⊢𝚷⁻{Γ}{l}{l'}{A}{B}{x} q₀ q₁ q₂ = ⊢𝚷
  (supp Γ)
  q₀
  λ y y#Γ → subst (λ B' → (Γ ⨟ y ∶[ l ] A) ⊢ B' ⦂ l')
    (ssb[] x (𝐯 y) B q₂)
    (rn⨟ q₁ y#Γ)

⊢𝛌⁻ :
  {l l' : ℕ}
  {Γ : Cx}
  {A : Ty}
  {B : Ty[ 1 ]}
  {b : Tm[ 1 ]}
  {x : 𝔸}
  (_ : (Γ ⨟ x ∶[ l ] A) ⊢ b [ x ] ∶[ l' ] B [ x ])
  (_ : x # (B , b))
  → ----------------------------------------------
  Γ ⊢ 𝛌 A b ∶[ max l l' ] 𝚷 l l' A B

⊢𝛌⁻{l}{l'}{Γ}{A}{B}{b}{x} q (x#B ∉∪ x#b)
  with ok⨟ q' x#Γ okΓ ← ⊢ok q = ⊢𝛌
  (supp Γ)
  (λ y y#Γ → subst₂ (λ b' B' → (Γ ⨟ y ∶[ l ] A) ⊢ b' ∶[ l' ] B')
    (ssb[] x (𝐯 y) b x#b)
    (ssb[] x (𝐯 y) B x#B)
    (rn⨟ q y#Γ))
  q'
  λ y y#Γ → subst (λ B' → (Γ ⨟ y ∶[ l ] A) ⊢ B' ⦂ l')
    (ssb[] x (𝐯 y) B x#B)
    (rn⨟ (⊢∶ty q) y#Γ)

⊢∙⁻ :
  {l l' : ℕ}
  {Γ : Cx}
  {A : Ty}
  {B : Ty[ 1 ]}
  {a b : Tm}
  {x : 𝔸}
  (_ : Γ ⊢ b ∶[ max l l' ] 𝚷 l l' A B)
  (_ : Γ ⊢ a ∶[ l ] A)
  (_ : (Γ ⨟ x ∶[ l ] A) ⊢ B [ x ] ⦂ l')
  (_ : x # B)
  → -----------------------------------
  Γ ⊢ b ∙[ A , B ] a ∶[ l' ] B [ a ]

⊢∙⁻{l}{l'}{Γ}{A}{B}{x = x} q₀ q₁ q₂ x#B = ⊢∙
  (supp Γ)
  q₀
  q₁
  (λ y y#Γ → subst (λ B' → (Γ ⨟ y ∶[ l ] A) ⊢ B' ⦂ l')
    (ssb[] x (𝐯 y) B x#B)
    (rn⨟ q₂ y#Γ))
  (⊢∶ty q₁)

⊢𝐄𝐪⁻ :
  {l : ℕ}
  {Γ : Cx}
  {A a b : Tm}
  (_ : Γ ⊢ a ∶[ l ] A)
  (_ : Γ ⊢ b ∶[ l ] A)
  → ------------------
  Γ ⊢ 𝐄𝐪 A a b ⦂ l

⊢𝐄𝐪⁻ q₀ q₁ = ⊢𝐄𝐪 q₀ q₁ (⊢∶ty q₀)

⊢𝐫𝐞𝐟𝐥⁻ :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶[ l ] A)
  → ---------------------------
  Γ ⊢ 𝐫𝐞𝐟𝐥 A a ∶[ l ] 𝐄𝐪 A a a

⊢𝐫𝐞𝐟𝐥⁻ q = ⊢𝐫𝐞𝐟𝐥 q (⊢∶ty q)

⊢𝐧𝐫𝐞𝐜⁻ :
  {l : ℕ}
  {Γ : Cx}
  {C : Ty[ 1 ]}
  {c₀ a : Tm}
  {c₊ : Tm[ 2 ]}
  {x y : 𝔸}
  (_ : Γ ⊢ c₀ ∶[ l ] C [ 𝐳𝐞𝐫𝐨 ])
  (_ : (Γ ⨟ x ∶[ 0 ] 𝐍𝐚𝐭 ⨟ y ∶[ l ] C [ x ]) ⊢
    c₊ [ x ][ y ] ∶[ l ] C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ])
  (_ : Γ ⊢ a ∶[ 0 ] 𝐍𝐚𝐭)
  (_ : x # (C , c₊))
  (_ : y # c₊)
  → -------------------------------------------
  Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶[ l ] C [ a ]

⊢𝐧𝐫𝐞𝐜⁻{l}{Γ}{C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ (x#C ∉∪ x#c₊) y#c₊
  with ok⨟ q (y#Γ ∉∪ y#x) (ok⨟ q' x#Γ okΓ) ← ⊢ok q₁ = ⊢𝐧𝐫𝐞𝐜
  (supp Γ)
  q₀
  (λ{x' y' (##:: y'#Γ (##:: (x'#y' ∉∪ x'#Γ) ##◇)) →
    subst₃ (λ C' c' C'' →
      (Γ ⨟ x' ∶[ 0 ] 𝐍𝐚𝐭 ⨟ y' ∶[ l ] C') ⊢ c' ∶[ l ] C'')
      (ssb[] x (𝐯 x') C x#C)
      (ssb[]² x y (𝐯 x') (𝐯 y') c₊ x#c₊ (y#c₊ ∉∪ y#x))
      (eq (𝐯 x') (𝐯 y'))
      (rn⨟² q₁ x'#Γ (#symm x'#y' ∉∪ y'#Γ))})
  q₂
  λ x' x'#Γ → subst (λ C' → (Γ ⨟ x' ∶[ 0 ] 𝐍𝐚𝐭) ⊢ C' ⦂ l)
    (ssb[] x (𝐯 x') C x#C)
    (rn⨟ q x'#Γ)
  where
  y#C : y # C
  y#C = ⊆∉ (⊢supp q₀ ∘ ∈∪₂ ∘ []supp C 𝐳𝐞𝐫𝐨) y#Γ
  y#Cs : y # C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
  y#Cs = ⊆∉ (supp[] C (𝐬𝐮𝐜𝐜 (𝐯 x))) (y#C ∉∪ y#x ∉∪ ∉∅)

  eq : ∀ a' b' →
    (x := a' ∘/ y := b') * C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ≡ C [ 𝐬𝐮𝐜𝐜 a' ]
  eq a' b' =
    begin
      (x := a' ∘/ y := b')* C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
    ≡⟨ updateFresh (x := a') y b' (C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]) y#Cs  ⟩
      (x := a') * C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
    ≡⟨ sb[] (x := a') C (𝐬𝐮𝐜𝐜 (𝐯 x)) ⟩
      ((x := a') * C) [ (x := a') * (𝐬𝐮𝐜𝐜 (𝐯 x)) ]
    ≡⟨ (cong (_[ (x := a') * 𝐬𝐮𝐜𝐜 (𝐯 x) ])) (ssbFresh x a' C x#C) ⟩
      C [ (x := a') * (𝐬𝐮𝐜𝐜 (𝐯 x)) ]
    ≡⟨⟩
      C [ 𝐬𝐮𝐜𝐜 ((x := a') * 𝐯 x) ]
    ≡⟨ cong (λ d → C [ 𝐬𝐮𝐜𝐜 d ]) (updateEq{σ = id}{a'} x) ⟩
      C [ 𝐬𝐮𝐜𝐜 a' ]
    ∎

𝚷Cong⁻ :
  {l l' : ℕ}
  {Γ : Cx}
  {A A' : Ty}
  {B B' : Ty[ 1 ]}
  {x : 𝔸}
  (_ : Γ ⊢ A ＝ A' ⦂ l)
  (_ : (Γ ⨟ x ∶[ l ] A) ⊢
    B [ x ] ＝ B' [ x ] ⦂ l')
  (_ : x # (B , B'))
  → -----------------------------------------
  Γ ⊢ 𝚷 l l' A B ＝ 𝚷 l l' A' B' ⦂ (max l l')

𝚷Cong⁻{l}{l'}{Γ}{A}{A'}{B}{B'}{x}  q₀ q₁ (x#B ∉∪ x#B') = 𝚷Cong
  (supp Γ)
  q₀
  (λ x' x'#Γ → subst₂ (λ C C' → (Γ ⨟ x' ∶[ l ] A) ⊢ C ＝ C' ⦂ l')
    (ssb[] x (𝐯 x') B x#B)
    (ssb[] x (𝐯 x') B' x#B')
    (rn⨟ q₁ x'#Γ))
  (⊢ty₁ q₀)

𝛌Cong⁻ :
  {l l' : ℕ}
  {Γ : Cx}
  {A A' : Ty}
  {B : Ty[ 1 ]}
  {b b' : Tm[ 1 ]}
  {x : 𝔸}
  (_ : Γ ⊢ A ＝ A' ⦂ l)
  (_ : (Γ ⨟ x ∶[ l ] A) ⊢
    b [ x ] ＝ b' [ x ] ∶[ l' ] B [ x ])
  (_ : x # (B , b , b'))
  → --------------------------------------------
  Γ ⊢ 𝛌 A b ＝ 𝛌 A' b' ∶[ max l l' ] 𝚷 l l' A B

𝛌Cong⁻{l}{l'}{Γ}{A}{A'}{B}{b}{b'}{x} q₀ q₁ (x#B ∉∪ x#b ∉∪ x#b') = 𝛌Cong
  (supp Γ)
  q₀
  (λ x' x'#Γ → subst₃ (λ c c' C →
    (Γ ⨟ x' ∶[ l ] A) ⊢ c ＝ c' ∶[ l' ] C)
    (ssb[] x (𝐯 x') b x#b)
    (ssb[] x (𝐯 x') b' x#b')
    (ssb[] x (𝐯 x') B x#B)
    (rn⨟ q₁ x'#Γ))
  (⊢ty₁ q₀)
  λ x' x'#Γ →
    subst (λ C → (Γ ⨟ x' ∶[ l ] A) ⊢ C ⦂ l')
    (ssb[] x (𝐯 x') B x#B)
    (rn⨟ (⊢∶ty (⊢ty₁ q₁)) x'#Γ)

∙Cong⁻ :
  {l l' : ℕ}
  {Γ : Cx}
  {A A' : Ty}
  {B B' : Ty[ 1 ]}
  {a a' b b' : Tm}
  {x : 𝔸}
  (_ : Γ ⊢ A ＝ A' ⦂ l)
  (_ : (Γ ⨟ x ∶[ l ] A) ⊢ B [ x ] ＝ B' [ x ] ⦂ l')
  (_ : Γ ⊢ b ＝ b' ∶[  max l l' ] 𝚷 l l' A B)
  (_ : Γ ⊢ a ＝ a' ∶[ l ] A)
  (_ : x # (B , B'))
  → ------------------------------------------------------
  Γ ⊢ b ∙[ A , B ] a ＝ b' ∙[ A' , B' ] a' ∶[ l' ] B [ a ]

∙Cong⁻{l}{l'}{Γ}{A}{A'}{B}{B'}{a}{a'}{b}{b'}{x}
  q₀ q₁ q₂ q₃ (x#B ∉∪ x#B') = ∙Cong
  (supp Γ)
  q₀
  (λ x' x'#Γ → subst₂ (λ C C' →
    (Γ ⨟ x' ∶[ l ] A) ⊢ C ＝ C' ⦂ l')
    (ssb[] x (𝐯 x') B x#B)
    (ssb[] x (𝐯 x') B' x#B')
    (rn⨟ q₁ x'#Γ))
  q₂
  q₃
  (⊢ty₁ q₀)
  λ x' x'#Γ → subst (λ C →
    (Γ ⨟ x' ∶[ l ] A) ⊢ C ⦂ l')
    (ssb[] x (𝐯 x') B x#B)
    (rn⨟ (⊢ty₁ q₁) x'#Γ)

𝐧𝐫𝐞𝐜Cong⁻ :
  {l : ℕ}
  {Γ : Cx}
  {C C' : Ty[ 1 ]}
  {c₀ c₀' a a'  : Tm}
  {c₊ c₊' : Tm[ 2 ]}
  {x y : 𝔸}
  (_ : (Γ ⨟ x ∶[ 0 ] 𝐍𝐚𝐭) ⊢ C [ x ] ＝ C' [ x ] ⦂ l)
  (_ : Γ ⊢ c₀ ＝ c₀' ∶[ l ] C [ 𝐳𝐞𝐫𝐨 ])
  (_ : (Γ ⨟ x ∶[ 0 ] 𝐍𝐚𝐭 ⨟ y ∶[ l ] C [ x ]) ⊢
    c₊ [ x ][ y ] ＝ c₊' [ x ][ y ] ∶[ l ] C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ])
  (_ : Γ ⊢ a ＝ a' ∶[ 0 ] 𝐍𝐚𝐭)
  (_ : x # (C , C' , c₊ , c₊'))
  (_ : y # (c₊ , c₊'))
  → --------------------------------------------------------
  Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ＝ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶[ l ] C [ a ]

𝐧𝐫𝐞𝐜Cong⁻{l}{Γ}{C}{C'}{c₀}{c₀'}{a}{a'}{c₊}{c₊'}{x}{y}
  q₀ q₁ q₂ q₃ (x#C ∉∪ x#C' ∉∪ x#c₊ ∉∪ x#c₊') (y#c₊ ∉∪ y#c₊')
  with ok⨟ q (y#Γ ∉∪ y#x) (ok⨟ q' x#Γ okΓ) ← ⊢ok q₂ = 𝐧𝐫𝐞𝐜Cong
  (supp Γ)
  (λ x' x'#Γ → subst₂ (λ D D' →
    (Γ ⨟ x' ∶[ 0 ] 𝐍𝐚𝐭) ⊢ D ＝ D' ⦂ l)
    (ssb[] x (𝐯 x') C x#C)
    (ssb[] x (𝐯 x') C' x#C')
    (rn⨟ q₀ x'#Γ))
  q₁
  (λ{x' y' (##:: y'#Γ (##:: (x'#y' ∉∪ x'#Γ) ##◇)) →
    subst₄ (λ D d d' D' →
      (Γ ⨟ x' ∶[ 0 ] 𝐍𝐚𝐭 ⨟ y' ∶[ l ] D) ⊢ d ＝ d' ∶[ l ] D')
      (ssb[] x (𝐯 x') C x#C)
      (ssb[]² x y (𝐯 x') (𝐯 y') c₊ x#c₊ (y#c₊ ∉∪ y#x))
      (ssb[]² x y (𝐯 x') (𝐯 y') c₊' x#c₊' (y#c₊' ∉∪ y#x))
      (eq (𝐯 x') (𝐯 y'))
      (rn⨟² q₂ x'#Γ (#symm x'#y' ∉∪ y'#Γ))})
  q₃
  λ x' x'#Γ → subst (λ C' → (Γ ⨟ x' ∶[ 0 ] 𝐍𝐚𝐭) ⊢ C' ⦂ l)
    (ssb[] x (𝐯 x') C x#C)
    (rn⨟ q x'#Γ)
  where
  y#C : y # C
  y#C = ⊆∉ (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₂ ∘ []supp C 𝐳𝐞𝐫𝐨) y#Γ
  y#Cs : y # C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
  y#Cs = ⊆∉ (supp[] C (𝐬𝐮𝐜𝐜 (𝐯 x))) (y#C ∉∪ y#x ∉∪ ∉∅)

  eq : ∀ a' b' →
    (x := a' ∘/ y := b') * C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ≡ C [ 𝐬𝐮𝐜𝐜 a' ]
  eq a' b' =
    begin
      (x := a' ∘/ y := b')* C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
    ≡⟨ updateFresh (x := a') y b' (C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]) y#Cs  ⟩
      (x := a') * C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
    ≡⟨ sb[] (x := a') C (𝐬𝐮𝐜𝐜 (𝐯 x)) ⟩
      ((x := a') * C) [ (x := a') * (𝐬𝐮𝐜𝐜 (𝐯 x)) ]
    ≡⟨ (cong (_[ (x := a') * 𝐬𝐮𝐜𝐜 (𝐯 x) ])) (ssbFresh x a' C x#C) ⟩
      C [ (x := a') * (𝐬𝐮𝐜𝐜 (𝐯 x)) ]
    ≡⟨⟩
      C [ 𝐬𝐮𝐜𝐜 ((x := a') * 𝐯 x) ]
    ≡⟨ cong (λ d → C [ 𝐬𝐮𝐜𝐜 d ]) (updateEq{σ = id}{a'} x) ⟩
      C [ 𝐬𝐮𝐜𝐜 a' ]
    ∎

𝚷Beta⁻ :
  {l l' : ℕ}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  {B : Ty[ 1 ]}
  {b : Tm[ 1 ]}
  {x : 𝔸}
  (_ : (Γ ⨟ x ∶[ l ] A) ⊢ b [ x ] ∶[ l' ] B [ x ])
  (_ : Γ ⊢ a ∶[ l ] A)
  (_ : x # (B , b))
  → -----------------------------------------------
  Γ ⊢ 𝛌 A b ∙[ A , B ] a ＝ b [ a ] ∶[ l' ] B [ a ]

𝚷Beta⁻{l}{l'}{Γ}{A}{a}{B}{b}{x} q₀ q₁ (x#B ∉∪ x#b) = 𝚷Beta
  (supp Γ)
  (λ x' x'#Γ → subst₂ (λ c C →
    (Γ ⨟ x' ∶[ l ] A) ⊢ c ∶[ l' ] C)
    (ssb[] x (𝐯 x') b x#b)
    (ssb[] x (𝐯 x') B x#B)
    (rn⨟ q₀ x'#Γ))
  q₁
  (⊢∶ty q₁)
  λ x' x'#Γ → subst (λ C →
    (Γ ⨟ x' ∶[ l ] A) ⊢ C ⦂ l')
    (ssb[] x (𝐯 x') B x#B)
    (rn⨟ (⊢∶ty q₀) x'#Γ)

𝐍𝐚𝐭Beta₀⁻ :
  {l : ℕ}
  {Γ : Cx}
  {C : Ty[ 1 ]}
  {c₀ : Tm}
  {c₊ : Tm[ 2 ]}
  {x y : 𝔸}
  (_ : Γ ⊢ c₀ ∶[ l ] C [ 𝐳𝐞𝐫𝐨 ])
  (_ : (Γ ⨟ x ∶[ 0 ] 𝐍𝐚𝐭 ⨟ y ∶[ l ] C [ x ]) ⊢
    c₊ [ x ][ y ] ∶[ l ] C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ])
  (_ : x # (C , c₊))
  (_ : y # c₊)
  → -------------------------------------------
  Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ 𝐳𝐞𝐫𝐨 ＝ c₀ ∶[ l ] C [ 𝐳𝐞𝐫𝐨 ]

𝐍𝐚𝐭Beta₀⁻{l}{Γ}{C}{c₀}{c₊}{x}{y} q₀ q₁ (x#C ∉∪ x#c₊) y#c₊
  with ok⨟ q (y#Γ ∉∪ y#x) (ok⨟ q' x#Γ okΓ) ← ⊢ok q₁ = 𝐍𝐚𝐭Beta₀
  (supp Γ)
  q₀
  (λ{x' y' (##:: y'#Γ (##:: (x'#y' ∉∪ x'#Γ) ##◇)) →
    subst₃ (λ C' c' C'' →
      (Γ ⨟ x' ∶[ 0 ] 𝐍𝐚𝐭 ⨟ y' ∶[ l ] C') ⊢ c' ∶[ l ] C'')
      (ssb[] x (𝐯 x') C x#C)
      (ssb[]² x y (𝐯 x') (𝐯 y') c₊ x#c₊ (y#c₊ ∉∪ y#x))
      (eq (𝐯 x') (𝐯 y'))
      (rn⨟² q₁ x'#Γ (#symm x'#y' ∉∪ y'#Γ))})
  λ x' x'#Γ → subst (λ C' → (Γ ⨟ x' ∶[ 0 ] 𝐍𝐚𝐭) ⊢ C' ⦂ l)
    (ssb[] x (𝐯 x') C x#C)
    (rn⨟ q x'#Γ)
  where
  y#C : y # C
  y#C = ⊆∉ (⊢supp q₀ ∘ ∈∪₂ ∘ []supp C 𝐳𝐞𝐫𝐨) y#Γ
  y#Cs : y # C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
  y#Cs = ⊆∉ (supp[] C (𝐬𝐮𝐜𝐜 (𝐯 x))) (y#C ∉∪ y#x ∉∪ ∉∅)

  eq : ∀ a' b' →
    (x := a' ∘/ y := b') * C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ≡ C [ 𝐬𝐮𝐜𝐜 a' ]
  eq a' b' =
    begin
      (x := a' ∘/ y := b')* C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
    ≡⟨ updateFresh (x := a') y b' (C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]) y#Cs  ⟩
      (x := a') * C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
    ≡⟨ sb[] (x := a') C (𝐬𝐮𝐜𝐜 (𝐯 x)) ⟩
      ((x := a') * C) [ (x := a') * (𝐬𝐮𝐜𝐜 (𝐯 x)) ]
    ≡⟨ (cong (_[ (x := a') * 𝐬𝐮𝐜𝐜 (𝐯 x) ])) (ssbFresh x a' C x#C) ⟩
      C [ (x := a') * (𝐬𝐮𝐜𝐜 (𝐯 x)) ]
    ≡⟨⟩
      C [ 𝐬𝐮𝐜𝐜 ((x := a') * 𝐯 x) ]
    ≡⟨ cong (λ d → C [ 𝐬𝐮𝐜𝐜 d ]) (updateEq{σ = id}{a'} x) ⟩
      C [ 𝐬𝐮𝐜𝐜 a' ]
    ∎

𝐍𝐚𝐭Beta₊⁻ :
  {l : ℕ}
  {Γ : Cx}
  {C : Ty[ 1 ]}
  {c₀ a : Tm}
  {c₊ : Tm[ 2 ]}
  {x y : 𝔸}
  (_ : Γ ⊢ c₀ ∶[ l ] C [ 𝐳𝐞𝐫𝐨 ])
  (_ : (Γ ⨟ x ∶[ 0 ] 𝐍𝐚𝐭 ⨟ y ∶[ l ] C [ x ]) ⊢
    c₊ [ x ][ y ] ∶[ l ] C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ])
  (_ : Γ ⊢ a ∶[ 0 ] 𝐍𝐚𝐭)
  (_ : x # (C , c₊))
  (_ : y # c₊)
  → --------------------------------------------
  Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
  c₊ [ a ][ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ] ∶[ l ] C [ 𝐬𝐮𝐜𝐜 a ]

𝐍𝐚𝐭Beta₊⁻{l}{Γ}{C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ (x#C ∉∪ x#c₊) y#c₊
  with ok⨟ q (y#Γ ∉∪ y#x) (ok⨟ q' x#Γ okΓ) ← ⊢ok q₁ = 𝐍𝐚𝐭Beta₊
  (supp Γ)
  q₀
  (λ{x' y' (##:: y'#Γ (##:: (x'#y' ∉∪ x'#Γ) ##◇)) →
    subst₃ (λ C' c' C'' →
      (Γ ⨟ x' ∶[ 0 ] 𝐍𝐚𝐭 ⨟ y' ∶[ l ] C') ⊢ c' ∶[ l ] C'')
      (ssb[] x (𝐯 x') C x#C)
      (ssb[]² x y (𝐯 x') (𝐯 y') c₊ x#c₊ (y#c₊ ∉∪ y#x))
      (eq (𝐯 x') (𝐯 y'))
      (rn⨟² q₁ x'#Γ (#symm x'#y' ∉∪ y'#Γ))})
  q₂
  (λ x' x'#Γ → subst (λ C' → (Γ ⨟ x' ∶[ 0 ] 𝐍𝐚𝐭) ⊢ C' ⦂ l)
    (ssb[] x (𝐯 x') C x#C)
    (rn⨟ q x'#Γ))
  where
  y#C : y # C
  y#C = ⊆∉ (⊢supp q₀ ∘ ∈∪₂ ∘ []supp C 𝐳𝐞𝐫𝐨) y#Γ
  y#Cs : y # C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
  y#Cs = ⊆∉ (supp[] C (𝐬𝐮𝐜𝐜 (𝐯 x))) (y#C ∉∪ y#x ∉∪ ∉∅)

  eq : ∀ a' b' →
    (x := a' ∘/ y := b') * C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ≡ C [ 𝐬𝐮𝐜𝐜 a' ]
  eq a' b' =
    begin
      (x := a' ∘/ y := b')* C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
    ≡⟨ updateFresh (x := a') y b' (C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]) y#Cs  ⟩
      (x := a') * C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
    ≡⟨ sb[] (x := a') C (𝐬𝐮𝐜𝐜 (𝐯 x)) ⟩
      ((x := a') * C) [ (x := a') * (𝐬𝐮𝐜𝐜 (𝐯 x)) ]
    ≡⟨ (cong (_[ (x := a') * 𝐬𝐮𝐜𝐜 (𝐯 x) ])) (ssbFresh x a' C x#C) ⟩
      C [ (x := a') * (𝐬𝐮𝐜𝐜 (𝐯 x)) ]
    ≡⟨⟩
      C [ 𝐬𝐮𝐜𝐜 ((x := a') * 𝐯 x) ]
    ≡⟨ cong (λ d → C [ 𝐬𝐮𝐜𝐜 d ]) (updateEq{σ = id}{a'} x) ⟩
      C [ 𝐬𝐮𝐜𝐜 a' ]
    ∎

𝚷⁻¹ :
  {l l' l'' : ℕ}
  {Γ : Cx}
  {A C : Ty}
  {B : Ty[ 1 ]}
  {x : 𝔸}
  (_ : Γ ⊢ 𝚷 l l' A B ∶[ l'' ] C)
  (_ : x # Γ)
  → -----------------------------
  (Γ ⨟ x ∶[ l ] A) ⊢ B [ x ] ⦂ l'

𝚷⁻¹ (⊢conv q _) x# = 𝚷⁻¹ q x#
𝚷⁻¹{l}{l'}{Γ = Γ}{A}{B = B}{x} (⊢𝚷 S q₀ q₁) x#Γ
  with (x' , x'#S ∉∪ x'#B) ← fresh (S , B) =
  subst (λ B' → (Γ ⨟ x ∶[ l ] A) ⊢ B' ⦂ l')
    ((ssb[] x' (𝐯 x) B x'#B))
    (rn⨟ (q₁ x' x'#S) x#Γ)

𝚷Eta⁻ :
  {l l' : ℕ}
  {Γ : Cx}
  {A : Ty}
  {B : Ty[ 1 ]}
  {b : Tm}
  {x : 𝔸}
  (_ : Γ ⊢ b ∶[ max l l' ] 𝚷 l l' A B)
  (_ : x # Γ)
  → --------------------------------------------------------------
  Γ ⊢ b ＝ 𝛌 A (x ． (b ∙[ A , B ] 𝐯 x)) ∶[ max l l' ] 𝚷 l  l' A B

𝚷Eta⁻{l}{l'}{Γ}{A}{B}{b}{x} q x#Γ
  with (x' , x'#Γ ∉∪ x'#x) ← fresh (Γ , x) =
  𝚷Eta (supp (Γ , x))
    q
    q'
    (λ y y# → Symm (q'' y y#))
    ⊢A
    λ y y# → ⊢∶ty (⊢ty₁ (q'' y y#))
  where
  x#b : x # b
  x#b = ⊆∉ (⊢supp q ∘ ∈∪₁) x#Γ
  x#A : x # A
  x#A = ⊆∉ (⊢supp q ∘ ∈∪₂ ∘ ∈∪₁) x#Γ
  x#B : x # B
  x#B = ⊆∉ (⊢supp q ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁) x#Γ
  x'#B : x' # B
  x'#B = ⊆∉ (⊢supp q ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁) x'#Γ

  ⊢Bx' : (Γ ⨟ x' ∶[ l ] A) ⊢ B [ x' ] ⦂ l'
  ⊢Bx'  = 𝚷⁻¹ (⊢∶ty q) x'#Γ

  ⊢A : Γ ⊢ A ⦂ l
  ⊢A = π₁ (π₂ ([]⁻¹ (⊢ok ⊢Bx')))

  r : (Γ ⨟ x ∶[ l ] A) ⊢ b ∙[ A , B ] 𝐯 x ∶[ l' ] B [ x ]
  r = ⊢∙⁻ {x = x'}
    (▷Jg (proj ⊢A x#Γ) q)
    (⊢𝐯 (ok⨟ ⊢A x#Γ (⊢ok q)) isInNew)
    (▷Jg
          (▷⨟ (proj ⊢A x#Γ) ⊢A (x'#Γ ∉∪ x'#x) (▷Jg (proj ⊢A x#Γ) ⊢A))
          ⊢Bx')
    x'#B

  q' : Γ ⊢ 𝛌 A (x ． b ∙[ A , B ] 𝐯 x) ∶[ max l l' ] 𝚷 l l' A B
  q' = ⊢𝛌⁻{x = x}
    (subst (λ c → (Γ ⨟ x ∶[ l ] A) ⊢ c ∶[ l' ] B [ x ])
      (symm (concAbs' x (b ∙[ A , B ] 𝐯 x)))
      r)
    (x#B ∉∪ #abs x (b ∙[ A , B ] 𝐯 x))

  q'' : ∀ y → y # (Γ , x) → (Γ ⨟ y ∶[ l ] A) ⊢
    (𝛌 A (x ． (b ∙[ A , B ] 𝐯 x))) ∙[ A , B ] 𝐯 y ＝
    b ∙[ A , B ] 𝐯 y ∶[ l' ] B [ y ]
  q'' y (y#Γ ∉∪ y#x) = subst (λ b' →
    (Γ ⨟ y ∶[ l ] A) ⊢
      (𝛌 A (x ． (b ∙[ A , B ] 𝐯 x))) ∙[ A , B ] 𝐯 y ＝
      b'  ∶[ l' ] B [ y ])
    eq
    (𝚷Beta⁻{x = x}
      (subst (λ c → (Γ ⨟ y ∶[ l ] A ⨟ x ∶[ l ] A) ⊢ c ∶[ l' ] B [ x ])
        (symm (concAbs' x (b ∙[ A , B ] 𝐯 x)))
        (▷Jg
          (▷⨟ (proj ⊢A y#Γ) ⊢A (x#Γ ∉∪ #symm y#x) (▷Jg (proj ⊢A y#Γ) ⊢A))
          r))
      (⊢𝐯 (ok⨟ ⊢A y#Γ (⊢ok q)) isInNew)
      (x#B ∉∪ (#abs x (b ∙[ A , B ] 𝐯 x))))
    where
    eq : (x ． (b ∙[ A , B ] 𝐯 x)) [ y ] ≡ b ∙[ A , B ] 𝐯 y
    eq rewrite concAbs x (b ∙[ A , B ] 𝐯 x) (𝐯 y)
       | ssbFresh x (𝐯 y) b x#b
       | ssbFresh x (𝐯 y) A x#A
       | ssbFresh x (𝐯 y) B x#B
       | updateEq{σ = id}{𝐯 y} x = refl

Reflect⁻ :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  {a b e : Tm}
  (_ : Γ ⊢ a ∶[ l ] A)
  (_ : Γ ⊢ b ∶[ l ] A )
  (_ : Γ ⊢ e ∶[ l ] 𝐄𝐪 A a b)
  → --------------------------
  Γ ⊢ a ＝ b ∶[ l ] A

Reflect⁻ q₀ q₁ q₂ = Reflect q₀ q₁ q₂ (⊢∶ty q₀)

UIP⁻ :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  {a b e e' : Tm}
  (_ : Γ ⊢ a ∶[ l ] A)
  (_ : Γ ⊢ b ∶[ l ] A)
  (_ : Γ ⊢ e ∶[ l ] 𝐄𝐪 A a b)
  (_ : Γ ⊢ e' ∶[ l ] 𝐄𝐪 A a b)
  → --------------------------
  Γ ⊢ e ＝ e' ∶[ l ] 𝐄𝐪 A a b

UIP⁻ q₀ q₁ q₂ q₃ = UIP q₀ q₁ q₂ q₃ (⊢∶ty q₀)

Cx[]⁻ :
  {l : ℕ}
  {Γ Γ' : Cx}
  {A A' : Ty}
  {x : 𝔸}
  (_ : ⊢ Γ ＝ Γ')
  (_ : Γ ⊢ A ＝ A' ⦂ l)
  (_ : x # (Γ , Γ'))
  → --------------------------------------
  ⊢ (Γ ⨟ x ∶[ l ] A) ＝ (Γ' ⨟ x ∶[ l ] A')

Cx[]⁻ q₀ q₁ q₂ = ＝⨟ q₀ q₁ q₂ (⊢ty₁ q₁) (＝⊢ (⊢ty₂ q₁) (CxSymm q₀))
