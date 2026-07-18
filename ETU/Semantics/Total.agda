module ETU.Semantics.Total where

open import Prelude
open import Setoid
open import WSLN

open import ETU.Syntax
open import ETU.Judgement
open import ETU.Rules

open import ETU.Semantics.Relation
open import ETU.Semantics.Ok
open import ETU.Semantics.WellScoped
open import ETU.Semantics.SingleValued
open import ETU.Semantics.Weakening
open import ETU.Semantics.Substitution
open import ETU.Semantics.ExistsFresh

----------------------------------------------------------------------
-- The semantic relations are total on typeable expressions and are
-- sound for definitional equality
----------------------------------------------------------------------

-- Totality for contexts
tot⟦cx⟧ :
  {Γ : Cx}
  (_ : Ok Γ)
  → ----------
  ∑[ C ∈ ∣ 𝒞 ∣ ]
  ⟦ Γ cx⟧＝ C

-- Totality for terms
tot⟦tm⟧ :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A ⦂ l)
  → ---------------------------
  ∑[ C ∈ ∣ 𝒞 ∣ ]
  ∑[ T ∈ Fam l C ]
  ∑[ t ∈ Elt l C T ]
  ⟦ Γ ⊢[ l ] A ty⟧＝(C , T) ∧
  ⟦ Γ ⊢[ l ] a tm⟧＝(C , T , t)

-- Soundness of term definitional equality
conv⟦tm⟧ :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  → ------------------------------
  ∑[ C ∈ ∣ 𝒞 ∣ ]
  ∑[ T ∈ Fam l C ]
  ∑[ t ∈ Elt l C T ]
  ⟦ Γ ⊢[ l ] A ty⟧＝(C , T) ∧
  ⟦ Γ ⊢[ l ] a tm⟧＝(C , T , t) ∧
  ⟦ Γ ⊢[ l ] a' tm⟧＝ (C , T , t)

-- Conditional version of totality for terms
tot⟦tm⟧' :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  {C : ∣ 𝒞 ∣}
  {T : Fam l C}
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : ⟦ Γ ⊢[ l ] A ty⟧＝(C , T))
  → -----------------------------
  ∑[ t ∈ Elt l C T ]
  ⟦ Γ ⊢[ l ] a tm⟧＝(C , T , t)

tot⟦tm⟧'{l}{C = C}{T} p q =
  let
    (C' , T' , t' , q' , q'') = tot⟦tm⟧ p

    e : Σℱ𝒶𝓂 l ∋ (C' , T') ~ (C , T)
    e = sv⟦ty⟧ q' q

    t : Elt l C T
    t = coe (ℰ𝓁𝓉 l) e t'

    e' : Σℰ𝓁𝓉 l ∋ (C' , T' , t') ~ (C , T , t)
    e' = (π₁ e , π₂ e , coh (ℰ𝓁𝓉 l){C' , T'}{C , T} e t')
  in
  (t , resp⟦tm⟧ q'' e')

-- Conditional version of soundness of definitional equality for terms
conv⟦tm⟧' :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  {C : ∣ 𝒞 ∣}
  {T : Fam l C}
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  (_ : ⟦ Γ ⊢[ l ] A ty⟧＝(C , T))
  → -----------------------------
  ∑[ t ∈ Elt l C T ]
  ⟦ Γ ⊢[ l ] a tm⟧＝(C , T , t) ∧
  ⟦ Γ ⊢[ l ] a' tm⟧＝ (C , T , t)

conv⟦tm⟧'{l}{C = C}{T} p q =
  let
    (C' , T' , t' , q₀ , q₁ , q₂) = conv⟦tm⟧ p

    e : Σℱ𝒶𝓂 l ∋ (C' , T') ~ (C , T)
    e = sv⟦ty⟧ q₀ q

    t : Elt l C T
    t = coe (ℰ𝓁𝓉 l) e t'

    e' : Σℰ𝓁𝓉 l ∋ (C' , T' , t') ~ (C , T , t)
    e' = (π₁ e , π₂ e , coh (ℰ𝓁𝓉 l){C' , T'}{C , T} e t')
  in
  (t , resp⟦tm⟧ q₁ e' , resp⟦tm⟧ q₂ e')

-- Absolute version of totality for types
tot⟦ty⟧ :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  (_ : Γ ⊢ A ⦂ l)
  → ------------------------
  ∑[ C ∈ ∣ 𝒞 ∣ ]
  ∑[ T ∈ Fam l C ]
  ⟦ Γ ⊢[ l ] A ty⟧＝ (C , T)

tot⟦ty⟧{l} p =
  let
    (C , _ , t , q , q') = tot⟦tm⟧ p
    e = sv⟦ty⟧ q (⟦𝐔⟧ (ok⟦ty⟧ q))
  in
  (C , coe (ℰ𝓁𝓉 (1+ l)) e t ,
   resp⟦tm⟧ q' (rflᶜ C , π₂ e , coh (ℰ𝓁𝓉 (1+ l)) e t))

-- Conditional version of totality for types
tot⟦ty⟧' :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  {C : ∣ 𝒞 ∣}
  (_ : Γ ⊢ A ⦂ l)
  (_ : ⟦ Γ cx⟧＝ C)
  → ------------------------
  ∑[ T ∈ Fam l C ]
  ⟦ Γ ⊢[ l ] A ty⟧＝ (C , T)

tot⟦ty⟧' p q = tot⟦tm⟧' p (⟦𝐔⟧ q)

-- Absolute version of soundness of definitional equality for types
conv⟦ty⟧ :
  {l : ℕ}
  {Γ : Cx}
  {A A' : Ty}
  (_ : Γ ⊢ A ＝ A' ⦂ l)
  → --------------------------
  ∑[ C ∈ ∣ 𝒞 ∣ ]
  ∑[ T ∈ Fam l C ]
  ⟦ Γ ⊢[ l ] A ty⟧＝ (C , T) ∧
  ⟦ Γ ⊢[ l ] A' ty⟧＝ (C , T)

conv⟦ty⟧{l} p =
  let
    (C , T , t , q , q' , q'') = conv⟦tm⟧ p
    e = sv⟦ty⟧ q (⟦𝐔⟧ (ok⟦ty⟧ q))
  in
  (C , coe (ℰ𝓁𝓉 (1+ l)) e t ,
   resp⟦tm⟧ q' (rflᶜ C , π₂ e , coh (ℰ𝓁𝓉 (1+ l)) e t) ,
   resp⟦tm⟧ q'' (rflᶜ C , π₂ e , coh (ℰ𝓁𝓉 (1+ l)) e t))

-- Conditional soundness of definitional equality for types
conv⟦ty⟧' :
  {l : ℕ}
  {Γ : Cx}
  {A A' : Ty}
  {C : ∣ 𝒞 ∣}
  (_ : Γ ⊢ A ＝ A' ⦂ l)
  (_ : ⟦ Γ cx⟧＝ C)
  → ---------------------------
  ∑[ T ∈ Fam l C ]
  ⟦ Γ ⊢[ l ] A ty⟧＝ (C , T) ∧
  ⟦ Γ ⊢[ l ] A' ty⟧＝ (C , T)

conv⟦ty⟧' p q = conv⟦tm⟧' p (⟦𝐔⟧ q)

-- Absolute version of totality for variables
tot⟦vr⟧ :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  (_ : Ok Γ)
  (_ : (x , A , l) isIn Γ)
  → ---------------------------
  ∑[ C ∈ ∣ 𝒞 ∣ ]
  ∑[ T ∈ Fam l C ]
  ∑[ t ∈ Elt l C T ]
  ⟦ Γ ⊢[ l ] A ty⟧＝(C , T) ∧
  ⟦ Γ ⊢[ l ] x vr⟧＝(C , T , t)

tot⟦vr⟧ (ok⨟{l}{x = x} p p' _) isInNew =
  let (C , T , q) = tot⟦ty⟧ p in
  (C ⋉[ l ] T , 𝓅 T * T , 𝓆 T , wk⟦ty⟧ q q p' , ⟦new⟧ q p')

tot⟦vr⟧{l}{A = A}{x} (ok⨟{l'}{Γ}{A'}{x'} p₀ p₁ p₂) (isInOld p₃) =
  let
    (C' , T' , q₀) = tot⟦ty⟧ p₀

    (C , T , t , q₁ , q₁') = tot⟦vr⟧ p₂ p₃

    e : C' ~ᶜ C
    e = sv⟦cx⟧ (ok⟦ty⟧ q₀) (ok⟦ty⟧ q₁)

    T'' : Fam l' C
    T'' = coe (ℱ𝒶𝓂 l') e T'

    e' : Σℱ𝒶𝓂 l' ∋ (C' , T') ~ (C , T'')
    e' = (e , coh (ℱ𝒶𝓂 l') e T')

    q₂ : ⟦ Γ ⨟ x' ∶ A' ⦂ l' ⊢[ l ] A ty⟧＝
      (C ⋉[ l' ] T'' , 𝓅 T'' * T)
    q₂ = wk⟦ty⟧ (resp⟦ty⟧ q₀ e') q₁ p₁

    q₂' : ⟦ Γ ⨟ x' ∶ A' ⦂ l' ⊢[ l ] x vr⟧＝
      (C ⋉[ l' ] T'' , 𝓅 T'' * T , 𝓅 T'' *₁ t)
    q₂' = wk⟦vr⟧ (resp⟦ty⟧ q₀ e') q₁' p₁
  in
  (C ⋉[ l' ] T'' , 𝓅 T'' * T , 𝓅 T'' *₁ t , q₂ , q₂')

tot⟦cx⟧ ok◇ = (Unit , ⟦◇⟧)

tot⟦cx⟧ (ok⨟{l} q₀ q₁ _) =
  let (C , T , q) = tot⟦ty⟧ q₀ in
  (C ⋉[ l ] T , ⟦⨟⟧ q q₁)

tot⟦tm⟧ (⊢conv p₀ p₁) =
  let
    (C , T , t , q , q') = tot⟦tm⟧ p₀
    (T' , q₁ , q₂) = conv⟦ty⟧' p₁ (ok⟦ty⟧ q)
  in
  (C , T , t , resp⟦ty⟧ q₂ (sv⟦ty⟧ q₁ q) , q')

tot⟦tm⟧ (⊢𝐯 p₀ p₁) =
  let (C , T , t , q , q') = tot⟦vr⟧ p₀ p₁ in
  (C , T , t , q , ⟦𝐯⟧ q')

tot⟦tm⟧ (⊢𝐔{l} p) =
   let (C , q) = tot⟦cx⟧ p in
   (C , 𝒰𝓃𝒾𝓋 (1+ l) , 𝒰𝓃𝒾𝓋 l , ⟦𝐔⟧ q , ⟦𝐔⟧ q)

tot⟦tm⟧{Γ = Γ} (⊢𝚷{l}{l'}{B = B} X q₀ q₁)
  with (x , x#X ∉∪ x#B ∉∪ x#Γ) ← fresh (X , B , Γ) =
  let
    (C , S , q₀') = tot⟦ty⟧ q₀
    (T , q₁') = tot⟦ty⟧' (q₁ x x#X) (⟦⨟⟧ q₀' x#Γ)
  in
  (C , 𝒰𝓃𝒾𝓋 (max l l') , 𝒫𝒾 l l' S T ,
   ⟦𝐔⟧ (ok⟦ty⟧ q₀') , ⟦𝚷⟧⁻ q₀' q₁' x#B)

tot⟦tm⟧{Γ = Γ} (⊢𝛌{l}{l'}{B = B}{b} X q h₀ h₁)
  with (x , x#X ∉∪ x#B ∉∪ x#b ∉∪ x#Γ) ← fresh (X , B , b , Γ) =
  let
    (C , S , h₀') = tot⟦ty⟧ h₀
    (T , h₁') = tot⟦ty⟧' (h₁ x x#X) (⟦⨟⟧ h₀' x#Γ)
    (t , q') = tot⟦tm⟧' (q x x#X) h₁'
  in
  (C , 𝒫𝒾 l l' S T , 𝓁𝒶𝓂 l l' S t ,
    ⟦𝚷⟧⁻ h₀' h₁' x#B , ⟦𝛌⟧⁻ h₀' q' x#b)

tot⟦tm⟧{Γ = Γ} (⊢∙{l}{l'}{B = B} X q₀ q₁ q₂ h)
  with (x , x#X ∉∪ x#B ∉∪ x#Γ) ← fresh (X , B , Γ) =
  let
    (C , S , s , q₁ , q₁') = tot⟦tm⟧ q₁
    (T , q₂) = tot⟦ty⟧' (q₂ x x#X) (⟦⨟⟧ q₁ x#Γ)
    (t , q₀) = tot⟦tm⟧' q₀ (⟦𝚷⟧⁻ q₁ q₂ x#B)
  in
  (C , ⟪ s ⟫ * T , 𝒶𝓅𝓅 l l' S T t s ,
    ⟦conc⟧ B x q₂ q₁' x#B , ⟦∙⟧⁻ q₀ q₁ q₂ q₁' x#B)

tot⟦tm⟧ (⊢𝐄𝐪{l} p₀ p₁ p₂) =
  let
    (C , T , q₂) = tot⟦ty⟧ p₂
    (t , q₀) = tot⟦tm⟧' p₀ q₂
    (t' , q₁) = tot⟦tm⟧' p₁ q₂
  in
  (C , 𝒰𝓃𝒾𝓋 l , ℰ𝓆 l T t t' ,
    ⟦𝐔⟧ (ok⟦ty⟧ q₂) , ⟦𝐄𝐪⟧ q₂ q₀ q₁)

tot⟦tm⟧ (⊢𝐫𝐞𝐟𝐥{l} p _) =
  let (C , T , t , q , q') = tot⟦tm⟧ p in
  (C , ℰ𝓆 l T t t , 𝓇𝒻𝓁 l T t , ⟦𝐄𝐪⟧ q q' q' , ⟦𝐫𝐞𝐟𝐥⟧ q q')

tot⟦tm⟧ (⊢𝐄𝐦𝐩 p) =
  let (C , q) = tot⟦cx⟧ p in
  (C , 𝒰𝓃𝒾𝓋 0 , ℰ𝓂𝓅 , ⟦𝐔⟧ q , ⟦𝐄𝐦𝐩⟧ q)

tot⟦tm⟧ (⊢𝐞𝐦𝐩{l} p₀ p₁) =
  let
    (C , T , q) = tot⟦ty⟧ p₀
    (e , q')    = tot⟦tm⟧' p₁ (⟦𝐄𝐦𝐩⟧ (ok⟦ty⟧ q))
  in
  (C , T , ℯ𝓂𝓅 l T e , q , ⟦𝐞𝐦𝐩⟧ q q')

tot⟦tm⟧ (⊢𝐍𝐚𝐭 p) =
  let (C , q) = tot⟦cx⟧ p in
  (C , 𝒰𝓃𝒾𝓋 0 , 𝒩𝒶𝓉 , ⟦𝐔⟧ q , ⟦𝐍𝐚𝐭⟧ q)

tot⟦tm⟧ (⊢𝐳𝐞𝐫𝐨 p) =
  let (C , q) = tot⟦cx⟧ p in
  (C , 𝒩𝒶𝓉 , 𝓏ℯ𝓇ℴ , ⟦𝐍𝐚𝐭⟧ q , ⟦𝐳𝐞𝐫𝐨⟧ q)

tot⟦tm⟧ (⊢𝐬𝐮𝐜𝐜 p) =
  let
    (C , T , t' , q , q') = tot⟦tm⟧ p

    t : Elt 0 C 𝒩𝒶𝓉
    t = coe (ℰ𝓁𝓉 0) (sv⟦ty⟧ q (⟦𝐍𝐚𝐭⟧ (ok⟦ty⟧ q))) t'

    e : Σℰ𝓁𝓉 0 ∋ (C , T , t') ~ (C , 𝒩𝒶𝓉  , t)
    e = (rflᶜ C , π₂ (sv⟦ty⟧ q (⟦𝐍𝐚𝐭⟧ (ok⟦ty⟧ q))) ,
      coh (ℰ𝓁𝓉 0) (sv⟦ty⟧ q (⟦𝐍𝐚𝐭⟧ (ok⟦ty⟧ q))) t')
  in
  (C , 𝒩𝒶𝓉 , 𝓈𝓊𝒸𝒸 t , ⟦𝐍𝐚𝐭⟧ (ok⟦ty⟧ q) , ⟦𝐬𝐮𝐜𝐜⟧ (resp⟦tm⟧ q' e))

tot⟦tm⟧{Γ = Γ} (⊢𝐧𝐫𝐞𝐜{l}{B}{b₀}{a}{b₊} X q₀ q₁ q₂ h)
  with (y , y#X ∉∪ y#b₊ ∉∪ y#Γ) ← fresh (X , b₊ , Γ)
  with (x , x#y ∉∪ x#X ∉∪ x#B ∉∪ x#b₊ ∉∪ x#Γ) ←
    fresh (y , X , B , b₊ , Γ) =
  (C ,  ⟪ s ⟫ * S , 𝓃𝓇ℯ𝒸 l S s₀ s₊ s ,
    ⟦conc⟧ B x qS qs x#B ,
    ⟦𝐧𝐫𝐞𝐜⟧⁻ qS qs₀ qs₊ qs (x#B ∉∪ x#b₊) y#b₊)
  where
  r : ∑[ C ∈ ∣ 𝒞 ∣ ]
      ∑[ N ∈ Fam 0 C ]
      ∑[ t ∈ Elt 0 C N ]
      ⟦ Γ ⊢[ 0 ] 𝐍𝐚𝐭 ty⟧＝ (C , N) ∧
      ⟦ Γ ⊢[ 0 ] a tm⟧＝ (C , N , t)
  r = tot⟦tm⟧ q₂
  C = π₁ r
  N = π₁ (π₂ r)
  q = π₁ (π₂ (π₂ (π₂ r)))
  rS : ∑[ S ∈ Fam l (C ⋉[ 0 ] 𝒩𝒶𝓉) ]
       ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢[ l ] B [ x ] ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 , S)
  rS = tot⟦ty⟧' (h x x#X) (⟦⨟⟧ (⟦𝐍𝐚𝐭⟧ (ok⟦ty⟧ q)) x#Γ)
  S = π₁ rS
  qS = π₂ rS
  rs : ∑[ s ∈ Elt 0 C 𝒩𝒶𝓉 ]
       ⟦ Γ ⊢[ 0 ] a tm⟧＝ (C , 𝒩𝒶𝓉 , s)
  rs = tot⟦tm⟧' q₂ (⟦𝐍𝐚𝐭⟧ (ok⟦ty⟧ q))
  s = π₁ rs
  qs = π₂ rs
  r₀ : ∑[ s₀ ∈ (Elt l C (⟪ 𝓏ℯ𝓇ℴ ⟫ * S)) ]
       ⟦ Γ ⊢[ l ] b₀ tm⟧＝ (C , ⟪ 𝓏ℯ𝓇ℴ ⟫ * S , s₀)
  r₀ = tot⟦tm⟧' q₀ (⟦conc⟧ B x qS (⟦𝐳𝐞𝐫𝐨⟧ (ok⟦ty⟧ q)) x#B)
  s₀ = π₁ r₀
  qs₀ = π₂ r₀
  T : Fam l (C ⋉[ 0 ] 𝒩𝒶𝓉)
  T = 𝒸ℴ𝓃𝓈 (𝓅 𝒩𝒶𝓉) (𝓈𝓊𝒸𝒸 (𝓆 𝒩𝒶𝓉)) * S
  q' : ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ B [ x ] ⦂ l ⊢[ l ]
    B [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S , 𝓅 S * T)
  q' = wk⟦ty⟧
    qS
    (subst (λ B' → ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢[ l ] B' ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 , T))
      (ssb[] x (𝐬𝐮𝐜𝐜 (𝐯 x)) B x#B)
      (sb⟦ty⟧
        (⟦sb⟧Update
          (wk⟦sb⟧ x (⟦id⟧ (ok⟦ty⟧ q)) (⟦𝐍𝐚𝐭⟧ (ok⟦ty⟧ q)) x#Γ)
          (⟦𝐍𝐚𝐭⟧ (ok⟦ty⟧ q))
          (⟦𝐬𝐮𝐜𝐜⟧ (⟦𝐯⟧ (⟦new⟧ (⟦𝐍𝐚𝐭⟧ (ok⟦ty⟧ q)) x#Γ)))
          x#Γ)
        qS))
    (y#Γ ∉∪ (#symm x#y))
  rs₊ : ∑[ s₊ ∈ Elt l (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S) (𝓅 S * T) ]
        ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ B [ x ] ⦂ l ⊢[ l ]
        b₊ [ x ][ y ] tm⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S , 𝓅 S * T , s₊)
  rs₊ = tot⟦tm⟧' (q₁ x y (##:: y#X (##:: (x#y ∉∪ x#X) ##◇))) q'
  s₊ = π₁ rs₊
  qs₊ = π₂ rs₊

conv⟦tm⟧ (Refl p) =
  let (C , T , t , q , q') = tot⟦tm⟧ p in
  (C , T , t , q , q' , q')

conv⟦tm⟧ (Symm p) =
  let (C , T , t , q , q' , q'') = conv⟦tm⟧ p in
  (C , T , t , q , q'' , q')

conv⟦tm⟧ (Trans p₀ p₁) =
  let
    (C , T , t , q , q₀ , q₀') = conv⟦tm⟧ p₀

    (t' , q₁ , q₁') = conv⟦tm⟧' p₁ q
  in
  (C , T , t , q , q₀ , resp⟦tm⟧ q₁' (sv⟦tm⟧ q₁ q₀'))

conv⟦tm⟧ (＝conv p₀ p₁) =
  let
    (C , T , t , q , q₁ , q₂) = conv⟦tm⟧ p₀

    (T' , q₁' , q₂') = conv⟦ty⟧' p₁ (ok⟦ty⟧ q)
  in
  (C , T , t , resp⟦ty⟧ q₂' (sv⟦ty⟧ q₁' q) , q₁ , q₂)

conv⟦tm⟧{Γ = Γ} (𝚷Cong{l}{l'}{B = B}{B'} X q₀ q₁ h)
  with (x , x#X ∉∪ x#B ∉∪ x#B' ∉∪ x#Γ) ← fresh (X , B , B' , Γ) =
  let
    (C , S , q) = tot⟦ty⟧ h
    (S' , qS , qS') = conv⟦ty⟧' q₀ (ok⟦ty⟧ q)
    (T , qT , qT') = conv⟦ty⟧' (q₁ x x#X) (⟦⨟⟧ q x#Γ)
    q' = resp⟦ty⟧ qS' (sv⟦ty⟧ qS q)
  in
  (C , 𝒰𝓃𝒾𝓋 (max l l') , 𝒫𝒾 l l' S T ,
    ⟦𝐔⟧ (ok⟦ty⟧ q) ,
    ⟦𝚷⟧⁻ q qT x#B ,
    ⟦𝚷⟧⁻ q' (sound⟦cx⟧ q q' qT') x#B')

conv⟦tm⟧{Γ = Γ} (𝛌Cong{l}{l'}{B = B}{b}{b'} X q₀ q₁ h₀ h₁)
  with (x , x#X ∉∪ x#B ∉∪ x#b ∉∪ x#b' ∉∪ x#Γ) ←
    fresh (X , B , b , b' , Γ) =
  let
    (C , S , q) = tot⟦ty⟧ h₀
    (T , qT) = tot⟦ty⟧' (h₁ x x#X) (⟦⨟⟧ q x#Γ)
    (S' , qS , qS') = conv⟦ty⟧' q₀ (ok⟦ty⟧ q)
    (t , qt , qt') = conv⟦tm⟧' (q₁ x x#X) qT
    q' = resp⟦ty⟧ qS' (sv⟦ty⟧ qS q)
  in
  (C , 𝒫𝒾 l l' S T , 𝓁𝒶𝓂 l l' S t ,
    ⟦𝚷⟧⁻ q qT x#B ,
    ⟦𝛌⟧⁻ q qt x#b ,
    ⟦𝛌⟧⁻ q' (sound⟦cx⟧ q q' qt') x#b')

conv⟦tm⟧{Γ = Γ} (∙Cong{l}{l'}{B = B}{B'} X q₀ q₁ q₂ q₃ h₀ h₁)
  with (x , x#X ∉∪ x#B ∉∪ x#B' ∉∪ x#Γ) ← fresh (X , B , B' , Γ) =
  let
    (C , S , qS , qS') = conv⟦ty⟧ q₀
    (T , qT  , qT') = conv⟦ty⟧' (q₁ x x#X) (⟦⨟⟧ qS x#Γ)
    (s , qs , qs') = conv⟦tm⟧' q₃ qS
    (t , qt , qt') = conv⟦tm⟧' q₂ (⟦𝚷⟧⁻ qS qT x#B)
  in
  (C , ⟪ s ⟫ * T , 𝒶𝓅𝓅 l l' S T t s ,
  ⟦conc⟧ B x qT qs x#B ,
  ⟦∙⟧⁻ qt qS qT qs x#B ,
  ⟦∙⟧⁻ qt' qS' (sound⟦cx⟧ qS qS' qT') qs' x#B')

conv⟦tm⟧ (𝐄𝐪Cong{l} q₀ q₁ q₂) =
  let
    (C , T , qT , qT') = conv⟦ty⟧ q₀
    (s , qs , qs') = conv⟦tm⟧' q₁ qT
    (t , qt , qt') = conv⟦tm⟧' q₂ qT
  in
  (C , 𝒰𝓃𝒾𝓋 l , ℰ𝓆 l T s t ,
    ⟦𝐔⟧ (ok⟦ty⟧ qT) ,
    ⟦𝐄𝐪⟧ qT qs qt ,
    ⟦𝐄𝐪⟧ qT' qs' qt')

conv⟦tm⟧ (𝐞𝐦𝐩Cong{l} q₀ q₁) =
  let
    (C , T , qT , qT') = conv⟦ty⟧ q₀
    (e , qe , qe') = conv⟦tm⟧' q₁ (⟦𝐄𝐦𝐩⟧ (ok⟦ty⟧ qT))
  in
  (C , T , ℯ𝓂𝓅 l T e , qT , ⟦𝐞𝐦𝐩⟧ qT qe , ⟦𝐞𝐦𝐩⟧ qT' qe')

conv⟦tm⟧ (𝐫𝐞𝐟𝐥Cong{l} q₀ q₁) =
  let
    (C , T , qT , qT') = conv⟦ty⟧ q₀
    (t , qt , qt') = conv⟦tm⟧' q₁ qT
  in
  (C , ℰ𝓆 l T t t , 𝓇𝒻𝓁 l T t ,
    ⟦𝐄𝐪⟧ qT qt qt ,
    ⟦𝐫𝐞𝐟𝐥⟧ qT qt ,
    ⟦𝐫𝐞𝐟𝐥⟧ qT' qt')

conv⟦tm⟧ (𝐬𝐮𝐜𝐜Cong q) =
  let
    (C , T , t' , qT , qt , qt') = conv⟦tm⟧ q
    q = ok⟦ty⟧ qT
    e = sv⟦ty⟧ qT (⟦𝐍𝐚𝐭⟧ q)
    t : Elt 0 C 𝒩𝒶𝓉
    t = coe (ℰ𝓁𝓉 0) e t'
    e' : Σℰ𝓁𝓉 0 ∋ (C , T , t') ~ (C , 𝒩𝒶𝓉  , t)
    e' = (rflᶜ C , π₂ e , coh (ℰ𝓁𝓉 0) e t')
  in
   (C ,  𝒩𝒶𝓉 , 𝓈𝓊𝒸𝒸 t ,
     ⟦𝐍𝐚𝐭⟧ q ,
     ⟦𝐬𝐮𝐜𝐜⟧ (resp⟦tm⟧ qt e') ,
     ⟦𝐬𝐮𝐜𝐜⟧ (resp⟦tm⟧ qt' e'))

conv⟦tm⟧{Γ = Γ} (𝐧𝐫𝐞𝐜Cong{l}{C = B}{B'}{b₀}{b₀'}{a}{a'}{b₊}{b₊'}
  X q₀ q₁ q₂ q₃ h)
  with (y , y#X ∉∪ y#b₊ ∉∪ y#b₊' ∉∪ y#Γ) ← fresh (X , b₊ , b₊' , Γ)
  with (x , x#y ∉∪ x#X ∉∪ x#B ∉∪ x#B' ∉∪ x#b₊ ∉∪ x#b₊' ∉∪ x#Γ) ←
    fresh (y , X , B , B' , b₊ , b₊' , Γ) =
  (C ,  ⟪ s ⟫ * S , 𝓃𝓇ℯ𝒸 l S s₀ s₊ s ,
    ⟦conc⟧ B x qS qs x#B  ,
    ⟦𝐧𝐫𝐞𝐜⟧⁻ qS qs₀ qs₊ qs (x#B ∉∪ x#b₊) y#b₊ ,
    ⟦𝐧𝐫𝐞𝐜⟧⁻{B = B'}{b₊ = b₊'}{s₊ = s₊}
    qS' qs₀' qs₊' qs' (x#B' ∉∪ x#b₊') y#b₊')
  where
  r : ∑[ C ∈ ∣ 𝒞 ∣ ]
      ∑[ N ∈ Fam 0 C ]
      ∑[ t ∈ Elt 0 C N ]
      ⟦ Γ ⊢[ 0 ] 𝐍𝐚𝐭 ty⟧＝ (C , N) ∧
      ⟦ Γ ⊢[ 0 ] a tm⟧＝ (C , N , t) ∧
      ⟦ Γ ⊢[ 0 ] a' tm⟧＝ (C , N , t)
  r = conv⟦tm⟧ q₃
  C = π₁ r
  N = π₁ (π₂ r)
  qN : ⟦ Γ ⊢[ 0 ] 𝐍𝐚𝐭 ty⟧＝ (C , N)
  qN = π₁ (π₂ (π₂ (π₂ r)))
  q : ⟦ Γ cx⟧＝ C
  q = ok⟦ty⟧ qN
  rS : ∑[ S ∈ Fam l (C ⋉[ 0 ] 𝒩𝒶𝓉) ]
       ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢[ l ] B [ x ] ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 , S) ∧
       ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢[ l ] B' [ x ] ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 , S)
  rS = conv⟦ty⟧' (q₀ x x#X) (⟦⨟⟧ (⟦𝐍𝐚𝐭⟧ q) x#Γ)
  S = π₁ rS
  qS = π₁ (π₂ rS)
  qS' = π₂ (π₂ rS)
  rs : ∑[ s ∈ Elt 0 C 𝒩𝒶𝓉 ]
       ⟦ Γ ⊢[ 0 ] a tm⟧＝ (C , 𝒩𝒶𝓉 , s) ∧
       ⟦ Γ ⊢[ 0 ] a' tm⟧＝ (C , 𝒩𝒶𝓉 , s)
  rs = conv⟦tm⟧' q₃ (⟦𝐍𝐚𝐭⟧ q)
  s = π₁ rs
  qs = π₁ (π₂ rs)
  qs' = π₂ (π₂ rs)
  r₀ :  ∑[ t ∈ Elt l C (⟪ 𝓏ℯ𝓇ℴ ⟫ * S) ]
        ⟦ Γ ⊢[ l ] b₀ tm⟧＝(C , (⟪ 𝓏ℯ𝓇ℴ ⟫ * S) , t) ∧
        ⟦ Γ ⊢[ l ] b₀' tm⟧＝ (C , (⟪ 𝓏ℯ𝓇ℴ ⟫ * S) , t)
  r₀ = conv⟦tm⟧' q₁ (⟦conc⟧ B x qS (⟦𝐳𝐞𝐫𝐨⟧ q) x#B)
  s₀ = π₁ r₀
  qs₀ = π₁ (π₂ r₀)
  qs₀' = π₂ (π₂ r₀)
  T : Fam l (C ⋉[ 0 ] 𝒩𝒶𝓉)
  T = 𝒸ℴ𝓃𝓈 (𝓅 𝒩𝒶𝓉) (𝓈𝓊𝒸𝒸 (𝓆 𝒩𝒶𝓉)) * S
  q' : ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ B [ x ] ⦂ l ⊢[ l ]
    B [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S , 𝓅 S * T)
  q' = wk⟦ty⟧
    qS
    (subst (λ B' → ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢[ l ] B' ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 , T))
      (ssb[] x (𝐬𝐮𝐜𝐜 (𝐯 x)) B x#B)
      (sb⟦ty⟧
        (⟦sb⟧Update
          (wk⟦sb⟧ x (⟦id⟧ q) (⟦𝐍𝐚𝐭⟧ q) x#Γ)
          (⟦𝐍𝐚𝐭⟧ q)
          (⟦𝐬𝐮𝐜𝐜⟧ (⟦𝐯⟧ (⟦new⟧ (⟦𝐍𝐚𝐭⟧ q) x#Γ)))
          x#Γ)
        qS))
    (y#Γ ∉∪ (#symm x#y))
  r₊ : ∑[ t ∈ (Elt l (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S) (𝓅 S * T)) ]
       ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ B [ x ] ⦂ l ⊢[ l ] b₊ [ x ][ y ] tm⟧＝
       (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S , 𝓅 S * T , t)
       ∧
       ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ B [ x ] ⦂ l ⊢[ l ] b₊' [ x ][ y ] tm⟧＝
       (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S , 𝓅 S * T , t)
  r₊ = conv⟦tm⟧' (q₂ x y (##:: y#X (##:: (x#y ∉∪ x#X) ##◇))) q'
  s₊ = π₁ r₊
  qs₊ = π₁ (π₂ r₊)
  qs₊' : ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ B' [ x ] ⦂ l ⊢[ l ] b₊' [ x ][ y ] tm⟧＝
    (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S , 𝓅 S * T , s₊)
  qs₊' = sound⟦cx⟧ qS qS' (π₂ (π₂ r₊))

conv⟦tm⟧{Γ = Γ} (𝚷Beta{l}{l'}{A}{a}{B}{b} X q₀ q₁ h₀ h₁)
  with (x , x#X ∉∪ x#B ∉∪ x#b ∉∪ x#Γ) ← fresh (X , B , b , Γ) =
  let
    (C , S , s , qS , qs) = tot⟦tm⟧ q₁
    (T , qT) = tot⟦ty⟧' (h₁ x x#X) (⟦⨟⟧ qS x#Γ)
    (t , qt) = tot⟦tm⟧' (q₀ x x#X) qT
  in
  (C , ⟪ s ⟫ * T , ⟪ s ⟫ *₁ t ,
    ⟦conc⟧ B x qT qs x#B ,
    resp⟦tm⟧
      (⟦∙⟧⁻ (⟦𝛌⟧⁻ qS qt x#b) qS qT qs x#B)
      (rflᶜ C  ,
       hrfl (ℱ𝒶𝓂 l') C (⟪ s ⟫ * T) ,
       𝒫𝒾𝒷ℯ𝓉𝒶 l l' S T t s) ,
    ⟦conc⟧ b x qt qs x#b)

conv⟦tm⟧{Γ = Γ} (𝐍𝐚𝐭Beta₀{l}{B}{b₀}{b₊} X q₀ q₁ h)
  with (y , y#X ∉∪ y#b₊ ∉∪ y#Γ) ← fresh (X , b₊ , Γ)
  with (x , x#y ∉∪ x#X ∉∪ x#B ∉∪ x#b₀ ∉∪ x#b₊ ∉∪ x#Γ) ←
    fresh (y , X , B , b₀ , b₊ , Γ) =
  (C , ⟪ 𝓏ℯ𝓇ℴ ⟫ * S , 𝓃𝓇ℯ𝒸 l S s₀ s₊ 𝓏ℯ𝓇ℴ ,
    ⟦conc⟧ B x qS (⟦𝐳𝐞𝐫𝐨⟧ q) x#B ,
    ⟦𝐧𝐫𝐞𝐜⟧⁻ qS qs₀ qs₊ (⟦𝐳𝐞𝐫𝐨⟧ q) (x#B ∉∪ x#b₊) y#b₊ ,
    qs₀)
  where
  r' : ∑[ C ∈ ∣ 𝒞 ∣ ]
       ∑[ T ∈ Fam l C ]
       ∑[ t ∈ Elt l C T ]
       ⟦ Γ ⊢[ l ] B [ 𝐳𝐞𝐫𝐨 ] ty⟧＝ (C , T) ∧
       ⟦ Γ ⊢[ l ] b₀ tm⟧＝ (C , T , t)
  r' = tot⟦tm⟧ q₀
  C = π₁ r'
  q₀' = π₁ (π₂ (π₂ (π₂ r')))
  q : ⟦ Γ cx⟧＝ C
  q = ok⟦ty⟧ q₀'
  r : ∑[ S ∈ Fam l (C ⋉[ 0 ] 𝒩𝒶𝓉) ]
      ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢[ l ] B [ x ] ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 , S)
  r = tot⟦ty⟧' (h x x#X) (⟦⨟⟧ (⟦𝐍𝐚𝐭⟧ q) x#Γ)
  S = π₁ r
  qS = π₂ r
  r₀ : ∑[ s₀ ∈ Elt l C (⟪ 𝓏ℯ𝓇ℴ ⟫ * S) ]
       ⟦ Γ ⊢[ l ] b₀ tm⟧＝ (C , ⟪ 𝓏ℯ𝓇ℴ ⟫ * S  , s₀)
  r₀ = tot⟦tm⟧' q₀ (⟦conc⟧ B x qS (⟦𝐳𝐞𝐫𝐨⟧ q) x#B)
  s₀ = π₁ r₀
  qs₀ = π₂ r₀
  T : Fam l (C ⋉[ 0 ] 𝒩𝒶𝓉)
  T = 𝒸ℴ𝓃𝓈 (𝓅 𝒩𝒶𝓉) (𝓈𝓊𝒸𝒸 (𝓆 𝒩𝒶𝓉)) * S
  q' : ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ B [ x ] ⦂ l ⊢[ l ]
    B [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S , 𝓅 S * T)
  q' = wk⟦ty⟧
    qS
    (subst (λ B' → ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢[ l ] B' ty⟧＝
      (C ⋉[ 0 ] 𝒩𝒶𝓉 , T))
      (ssb[] x (𝐬𝐮𝐜𝐜 (𝐯 x)) B x#B)
      (sb⟦ty⟧
        (⟦sb⟧Update
          (wk⟦sb⟧ x (⟦id⟧ q) (⟦𝐍𝐚𝐭⟧ q) x#Γ)
          (⟦𝐍𝐚𝐭⟧ q)
          (⟦𝐬𝐮𝐜𝐜⟧ (⟦𝐯⟧ (⟦new⟧ (⟦𝐍𝐚𝐭⟧ q) x#Γ)))
          x#Γ)
        qS))
    (y#Γ ∉∪ (#symm x#y))
  r₊ : ∑[ s₊ ∈ Elt l (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S) (𝓅 S * T) ]
       ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ B [ x ] ⦂ l ⊢[ l ]
       b₊ [ x ][ y ] tm⟧＝(C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S , 𝓅 S * T , s₊)
  r₊ = tot⟦tm⟧' (q₁ x y (##:: y#X (##:: (x#y ∉∪ x#X) ##◇))) q'
  s₊ = π₁ r₊
  qs₊ = π₂ r₊

conv⟦tm⟧{Γ = Γ} (𝐍𝐚𝐭Beta₊{l}{B}{b₀}{a}{b₊} X q₀ q₁ q₂ h)
  with (y , y#X ∉∪ y#b₊ ∉∪ y#Γ) ← fresh (X , b₊ , Γ)
  with (x , x#y ∉∪ x#X ∉∪ x#B ∉∪ x#b₀ ∉∪ x#b₊ ∉∪ x#Γ) ←
    fresh (y , X , B , b₀ , b₊ , Γ) =
  (C , ⟪ s ⟫ * T , 𝓃𝓇ℯ𝒸 l S s₀ s₊ (𝓈𝓊𝒸𝒸 s) ,
    ⟦conc⟧ B x qS (⟦𝐬𝐮𝐜𝐜⟧ qs) x#B ,
    ⟦𝐧𝐫𝐞𝐜⟧⁻ qS qs₀ qs₊ (⟦𝐬𝐮𝐜𝐜⟧ qs) (x#B ∉∪ x#b₊) y#b₊ ,
    q'')
  where
  r' : ∑[ C ∈ ∣ 𝒞 ∣ ]
       ∑[ T ∈ Fam l C ]
       ∑[ t ∈ Elt l C T ]
       ⟦ Γ ⊢[ l ] B [ 𝐳𝐞𝐫𝐨 ] ty⟧＝ (C , T) ∧
       ⟦ Γ ⊢[ l ] b₀ tm⟧＝ (C , T , t)
  r' = tot⟦tm⟧ q₀
  C = π₁ r'
  q₀' = π₁ (π₂ (π₂ (π₂ r')))
  q : ⟦ Γ cx⟧＝ C
  q = ok⟦ty⟧ q₀'
  r : ∑[ S ∈ Fam l (C ⋉[ 0 ] 𝒩𝒶𝓉) ]
      ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢[ l ] B [ x ] ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 , S)
  r = tot⟦ty⟧' (h x x#X) (⟦⨟⟧ (⟦𝐍𝐚𝐭⟧ q) x#Γ)
  S = π₁ r
  qS = π₂ r
  r₀ : ∑[ s₀ ∈ Elt l C (⟪ 𝓏ℯ𝓇ℴ ⟫ * S) ]
       ⟦ Γ ⊢[ l ] b₀ tm⟧＝ (C , ⟪ 𝓏ℯ𝓇ℴ ⟫ * S  , s₀)
  r₀ = tot⟦tm⟧' q₀ (⟦conc⟧ B x qS (⟦𝐳𝐞𝐫𝐨⟧ q) x#B)
  s₀ = π₁ r₀
  qs₀ = π₂ r₀
  T : Fam l (C ⋉[ 0 ] 𝒩𝒶𝓉)
  T = 𝒸ℴ𝓃𝓈 (𝓅 𝒩𝒶𝓉) (𝓈𝓊𝒸𝒸 (𝓆 𝒩𝒶𝓉)) * S
  q' : ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ B [ x ] ⦂ l ⊢[ l ]
    B [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ty⟧＝ (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S , 𝓅 S * T)
  q' = wk⟦ty⟧
    qS
    (subst (λ B' → ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢[ l ] B' ty⟧＝
      (C ⋉[ 0 ] 𝒩𝒶𝓉 , T))
      (ssb[] x (𝐬𝐮𝐜𝐜 (𝐯 x)) B x#B)
      (sb⟦ty⟧
        (⟦sb⟧Update
          (wk⟦sb⟧ x (⟦id⟧ q) (⟦𝐍𝐚𝐭⟧ q) x#Γ)
          (⟦𝐍𝐚𝐭⟧ q)
          (⟦𝐬𝐮𝐜𝐜⟧ (⟦𝐯⟧ (⟦new⟧ (⟦𝐍𝐚𝐭⟧ q) x#Γ)))
        x#Γ)
        qS))
    (y#Γ ∉∪ (#symm x#y))
  r₊ : ∑[ s₊ ∈ Elt l (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S) (𝓅 S * T) ]
       ⟦ Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ B [ x ] ⦂ l ⊢[ l ]
       b₊ [ x ][ y ] tm⟧＝(C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ l ] S , 𝓅 S * T , s₊)
  r₊ = tot⟦tm⟧' (q₁ x y (##:: y#X (##:: (x#y ∉∪ x#X) ##◇))) q'
  s₊ = π₁ r₊
  qs₊ = π₂ r₊
  rs : ∑[ s ∈ Elt 0 C  𝒩𝒶𝓉 ]
       ⟦  Γ ⊢[ 0 ] a tm⟧＝ (C , 𝒩𝒶𝓉 , s)
  rs = tot⟦tm⟧' q₂ (⟦𝐍𝐚𝐭⟧ q)
  s = π₁ rs
  qs = π₂ rs
  q'' : ⟦ Γ ⊢[ l ] b₊ [ a ][ 𝐧𝐫𝐞𝐜 B b₀ b₊ a ] tm⟧＝
    (C , ⟪ s ⟫ * T , 𝓃𝓇ℯ𝒸 l S s₀ s₊ (𝓈𝓊𝒸𝒸 s))
  q'' = resp⟦tm⟧
    (⟦conc⟧² b₊ x y qs₊ qs
      (⟦𝐧𝐫𝐞𝐜⟧⁻ qS qs₀ qs₊ qs (x#B ∉∪ x#b₊) y#b₊) x#b₊ y#b₊)
    (rflᶜ C ,
     hrfl (ℱ𝒶𝓂 l) C (⟪ s ⟫ * T) ,
     hrfl (ℰ𝓁𝓉 l) (C , ⟪ s ⟫ * T) (𝓃𝓇ℯ𝒸 l S s₀ s₊ (𝓈𝓊𝒸𝒸 s)))

conv⟦tm⟧ (Reflect{l} q₀ q₁ q₂ h) =
  let
    (C , T , qT) = tot⟦ty⟧ h
    (t , qt) = tot⟦tm⟧' q₀ qT
    (t' , qt') = tot⟦tm⟧' q₁ qT
    (e , qe) = tot⟦tm⟧' q₂ (⟦𝐄𝐪⟧ qT qt qt')
  in
  (C , T , t , qT , qt ,
    resp⟦tm⟧ qt'
      (rflᶜ C , hrfl (ℱ𝒶𝓂 l) C T ,
        hsym (ℰ𝓁𝓉 l){y = t}{t'}
          (rfl (Σℱ𝒶𝓂 l) (C , T))
          (𝓇ℯ𝒻𝓁ℯ𝒸𝓉 l T t t' e)))

conv⟦tm⟧ (UIP{l} q₀ q₁ q₂ q₃ h) =
  let
    (C , T , qT) = tot⟦ty⟧ h
    (t , qt) = tot⟦tm⟧' q₀ qT
    (t' , qt') = tot⟦tm⟧' q₁ qT
    (e , qe) = tot⟦tm⟧' q₂ (⟦𝐄𝐪⟧ qT qt qt')
    (e' , qe') = tot⟦tm⟧' q₃ (⟦𝐄𝐪⟧ qT qt qt')
  in
  (C , ℰ𝓆 l T t t' , e , ⟦𝐄𝐪⟧ qT qt qt' , qe , resp⟦tm⟧ qe'
    (rflᶜ C , hrfl (ℱ𝒶𝓂 l) C (ℰ𝓆 l T t t') ,
      hsym (ℰ𝓁𝓉 l){y = e}{e'}
        (rfl (Σℱ𝒶𝓂 l) (C , ℰ𝓆 l T t t'))
        (𝓊𝒾𝓅 l T t t' e e')))

conv⟦tm⟧{Γ = Γ} (𝚷Eta{l}{l'}{A}{B}{b}{b'} X q₀ q₁ q₂ h₀ h₁)
  with (x , x#X ∉∪ x#B ∉∪ x#Γ) ← fresh (X , B , Γ) =
  (C , 𝒫𝒾 l l' S T , t₀ , ⟦𝚷⟧⁻ qS qT x#B , qt₀ , q)
  where
  rh₀ : ∑[ C ∈ ∣ 𝒞 ∣ ]
      ∑[ S ∈ Fam l C ]
      ⟦ Γ ⊢[ l ] A ty⟧＝ (C , S)
  rh₀ = tot⟦ty⟧ h₀
  C : ∣ 𝒞 ∣
  C = π₁ rh₀
  S : Fam l C
  S = π₁ (π₂ rh₀)
  qS : ⟦ Γ ⊢[ l ] A ty⟧＝ (C , S)
  qS = π₂ (π₂ rh₀)

  rh₁ : ∑[ T ∈ Fam l' (C ⋉[ l ] S) ]
       ⟦ Γ ⨟ x ∶ A ⦂ l ⊢[ l' ] B [ x ] ty⟧＝ (C ⋉[ l ] S , T)
  rh₁ = tot⟦ty⟧' (h₁ x x#X) (⟦⨟⟧ qS x#Γ)
  T : Fam l' (C ⋉[ l ] S)
  T = π₁ rh₁
  qT : ⟦ Γ ⨟ x ∶ A ⦂ l ⊢[ l' ] B [ x ] ty⟧＝ (C ⋉[ l ] S , T)
  qT = π₂ rh₁

  r₀ : ∑[ t₀ ∈ Elt (max l l') C (𝒫𝒾 l l' S T) ]
       ⟦ Γ ⊢[ max l l' ] b tm⟧＝ (C , 𝒫𝒾 l l' S T , t₀)
  r₀ = tot⟦tm⟧' q₀ (⟦𝚷⟧⁻ qS qT x#B)
  t₀ : Elt (max l l') C (𝒫𝒾 l l' S T)
  t₀ = π₁ r₀
  qt₀ : ⟦ Γ ⊢[ max l l' ] b tm⟧＝ (C , 𝒫𝒾 l l' S T , t₀)
  qt₀ = π₂ r₀

  r₁ : ∑[ t₁ ∈ Elt (max l l') C (𝒫𝒾 l l' S T) ]
       ⟦ Γ ⊢[ max l l' ] b' tm⟧＝ (C , 𝒫𝒾 l l' S T , t₁)
  r₁ = tot⟦tm⟧' q₁ (⟦𝚷⟧⁻ qS qT x#B)
  t₁ : Elt (max l l') C (𝒫𝒾 l l' S T)
  t₁ = π₁ r₁
  qt₁ : ⟦ Γ ⊢[ max l l' ] b' tm⟧＝ (C , 𝒫𝒾 l l' S T , t₁)
  qt₁ = π₂ r₁

  re : ∑[ te ∈ Elt l' (C  ⋉[ l ] S) T ]
       (⟦ Γ ⨟ x ∶ A ⦂ l ⊢[ l' ] b ∙[ A , B ] 𝐯 x tm⟧＝
         (C ⋉[ l ] S , T , te))
       ∧
       (⟦ Γ ⨟ x ∶ A ⦂ l ⊢[ l' ] b' ∙[ A , B ] 𝐯 x tm⟧＝
         (C ⋉[ l ] S , T , te))
  re = conv⟦tm⟧' (q₂ x x#X) qT
  te : Elt l' (C  ⋉[ l ] S) T
  te = π₁ re
  qe₀ : ⟦ Γ ⨟ x ∶ A ⦂ l ⊢[ l' ] b ∙[ A , B ] 𝐯 x tm⟧＝
    (C ⋉[ l ] S , T , te)
  qe₀ = π₁ (π₂ re)
  qe₁ : ⟦ Γ ⨟ x ∶ A ⦂ l ⊢[ l' ] b' ∙[ A , B ] 𝐯 x tm⟧＝
    (C ⋉[ l ] S , T , te)
  qe₁ = π₂ (π₂ re)

  S' : Fam l (C ⋉[ l ] S)
  S' = 𝓅 S * S

  T' : Fam l' (C ⋉[ l ] S ⋉[ l ] S')
  T' = (𝓅 S ⋉′[ l ] S) * T

  t₀' : Elt (max l l') (C ⋉[ l ] S) (𝒫𝒾 l l' S' T')
  t₀' = coe (ℰ𝓁𝓉 (max l l'))
    ((rflᶜ (C ⋉[ l ] S) , ntrl𝒫𝒾 l l' S T (𝓅 S)))
    (𝓅 S *₁ t₀)

  t₁' : Elt (max l l') (C ⋉[ l ] S) (𝒫𝒾 l l' S' T')
  t₁' = coe (ℰ𝓁𝓉 (max l l'))
    ((rflᶜ (C ⋉[ l ] S) , ntrl𝒫𝒾 l l' S T (𝓅 S)))
    (𝓅 S *₁ t₁)

  qt₀' : ⟦ Γ ⨟ x ∶ A ⦂ l ⊢[ max l l' ] b tm⟧＝
    (C ⋉[ l ] S , 𝒫𝒾 l l' S' T' , t₀')
  qt₀' = resp⟦tm⟧
    (wk⟦tm⟧ qS qt₀ x#Γ)
    (rflᶜ (C ⋉[ l ] S) ,
     ntrl𝒫𝒾 l l' S T (𝓅 S) ,
     coh (ℰ𝓁𝓉 (max l l'))
       {C ⋉[ l ] S , 𝓅 S *  𝒫𝒾 l l' S T}
       {C ⋉[ l ] S , 𝒫𝒾 l l' S' T'}
       ((rflᶜ (C ⋉[ l ] S) , ntrl𝒫𝒾 l l' S T (𝓅 S)))
       (𝓅 S *₁ t₀))

  qt₁' : ⟦ Γ ⨟ x ∶ A ⦂ l ⊢[ max l l' ] b' tm⟧＝
    (C ⋉[ l ] S , 𝒫𝒾 l l' S' T' , t₁')
  qt₁' = resp⟦tm⟧
    (wk⟦tm⟧ qS qt₁ x#Γ)
    (rflᶜ (C ⋉[ l ] S) ,
     ntrl𝒫𝒾 l l' S T (𝓅 S) ,
     coh (ℰ𝓁𝓉 (max l l'))
       {C ⋉[ l ] S , 𝓅 S *  𝒫𝒾 l l' S T}
       {C ⋉[ l ] S , 𝒫𝒾 l l' S' T'}
       ((rflᶜ (C ⋉[ l ] S) , ntrl𝒫𝒾 l l' S T (𝓅 S)))
       (𝓅 S *₁ t₁))

  qe₀' : ⟦ Γ ⨟ x ∶ A ⦂ l ⊢[ l' ] b ∙[ A , B ] 𝐯 x tm⟧＝
    (C ⋉[ l ] S , ⟪ 𝓆 S ⟫ * T' , 𝒶𝓅𝓅 l l' S' T' t₀' (𝓆 S))
  qe₀' = ⟦∙⟧{T = T'}
    (supp (Γ , x))
    qt₀' (wk⟦ty⟧ qS qS x#Γ)
    (λ{y (y#Γ ∉∪ y#x) →
      ▷⟦ty⟧
        (⟦▷⨟⟧
          (⟦proj⟧ qS x#Γ)
          qS
          (y#Γ ∉∪ y#x)
          (wk⟦ty⟧ qS qS x#Γ))
        (⟦α⟧ B x y qS qT x#B y#Γ)})
    (⟦𝐯⟧ (⟦new⟧ qS x#Γ))

  qe₁' : ⟦ Γ ⨟ x ∶ A ⦂ l ⊢[ l' ] b' ∙[ A , B ] 𝐯 x tm⟧＝
    (C ⋉[ l ] S , ⟪ 𝓆 S ⟫ * T' , 𝒶𝓅𝓅 l l' S' T' t₁' (𝓆 S))
  qe₁' = ⟦∙⟧{T = T'}
    (supp (Γ , x))
    qt₁' (wk⟦ty⟧ qS qS x#Γ)
    (λ{y (y#Γ ∉∪ y#x) →
      ▷⟦ty⟧
        (⟦▷⨟⟧
          (⟦proj⟧ qS x#Γ)
          qS
          (y#Γ ∉∪ y#x)
          (wk⟦ty⟧ qS qS x#Γ))
        (⟦α⟧ B x y qS qT x#B y#Γ)})
    (⟦𝐯⟧ (⟦new⟧ qS x#Γ))

  e₂ : ℰ𝓁𝓉 l' ∋
    (C ⋉[ l ] S , ⟪ 𝓆 S ⟫ * T') , 𝒶𝓅𝓅 l l' S' T' t₁' (𝓆 S)
    ≈
    (C ⋉[ l ] S , ⟪ 𝓆 S ⟫ * T') , 𝒶𝓅𝓅 l l' S' T' t₀' (𝓆 S)
  e₂ = htrs (ℰ𝓁𝓉 l')
    {C ⋉[ l ] S , ⟪ 𝓆 S ⟫ * T'}
    {C ⋉[ l ] S , T}
    {C ⋉[ l ] S , ⟪ 𝓆 S ⟫ * T'}
    {𝒶𝓅𝓅 l l' S' T' t₁' (𝓆 S)}
    {te}
    {𝒶𝓅𝓅 l l' S' T' t₀' (𝓆 S)}
    (rflᶜ (C ⋉[ l ] S) , hcng T)
    (rflᶜ (C ⋉[ l ] S) , hcng T)
    (π₂ (π₂ (sv⟦tm⟧ qe₁' qe₁)))
    (π₂ (π₂ (sv⟦tm⟧ qe₀ qe₀')))

  t₁₀ : (ℰ𝓁𝓉 (max l l')) ′ (C , 𝒫𝒾 l l' S T) ∋  t₁ ~  t₀
  t₁₀ c c' u = htrs (ℰ𝓁 (max l l'))
    {y' = ∥ 𝓁𝒶𝓂 l l' S {⟪ 𝓆 S ⟫ * T'} (𝒶𝓅𝓅 l l' S' T' t₀' (𝓆 S)) ∥ c}
    (PI.tyCong (pi l l') _ _ _ _ _ _
      (rfl (𝒰 l)
      (∥ S ∥ c))
      λ y y' v →
        hcng T (c , y) (c , y') (hrflᶜ C c , refl , v))
    (PI.tyCong (pi l l') _ _ _ _ _ _
      (hcng S c c' u)
      λ y y' v →
        hcng T (c , y) (c' , y') (u , refl , v))
    (htrs (ℰ𝓁 (max l l'))
      (PI.tyCong (pi l l') _ _ _ _ _ _
        (rfl (𝒰 l)
        (∥ S ∥ c))
        (λ y y' v →
          hcng T (c , y) (c , y') (hrflᶜ C c , refl , v)))
      (rfl (𝒰 (max l l')) (PI.ty (pi l l') (∥ S ∥ c)
        (λ z → ∥ T ∥ (c , z))
        (λ z z₁ e → hcng (⟪ 𝓆 S ⟫ * T') (c , z) (c , z₁)
          (hrflᶜ C c , refl , e))))
      (hsym (ℰ𝓁 (max l l'))
        (PI.tyCong (pi l l') _ _ _ _ _ _
          (rfl (𝒰 l)
          (∥ S ∥ c))
          (λ y y' v →
             hcng T (c , y) (c , y') (hrflᶜ C c , refl , v)))
        (𝒫𝒾ℰ𝓉𝒶.etaPf C l l' S T t₁ c c (hrflᶜ C c)))
      (PI.lamCong (pi l l') _ _ _ _ _ _ _ _ _ _
        (λ y y' v →
          e₂ (c , y) (c , y') (hrflᶜ C c , refl , v))))
    (𝒫𝒾ℰ𝓉𝒶.etaPf C l l' S T t₀ c c' u)

  q : ⟦ Γ ⊢[ max l l' ] b' tm⟧＝ (C , 𝒫𝒾 l l' S T , t₀)
  q = resp⟦tm⟧
    qt₁
    (rflᶜ C , ((hrfl (ℱ𝒶𝓂 (max l l')) C (𝒫𝒾 l l' S T)) , t₁₀))
