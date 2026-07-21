module Setoid.PiType where

open import Prelude

open import Setoid.Definition
open import Setoid.Display
open import Setoid.Universes
open import Setoid.Lift

----------------------------------------------------------------------
-- Helper structure for Pi-types
----------------------------------------------------------------------
record PI
  (A B : Setd)
  (EA : Setd[ A ])
  (EB : Setd[ B ])
  (n : ℕ)
  : --------------
  Set
  where
  constructor mkPI
  field
    ty :
      (X : ∣ A ∣)
      (Y : ∥ EA ∥ X → ∣ B ∣)
      (q :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → -----------------------
        B ∋ Y x ~ Y x'           )
      → --------------------------
      U n

    tyCong :
      (X X' : ∣ A ∣)
      (Y : ∥ EA ∥ X → ∣ B ∣)
      (Y' : ∥ EA ∥ X' → ∣ B ∣)
      (q :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → -----------------------
        B ∋ Y x ~ Y x'           )
      (q' :
        (x x' : ∥ EA ∥ X')
        (_ : EA ∋ X' , x ≈ X' , x')
        → -------------------------
        B ∋ Y' x ~ Y' x'           )
      (_ : A ∋ X ~ X')
      (_ :
        (x : ∥ EA ∥ X)
        (x' : ∥ EA ∥ X')
        (_ : EA ∋ X , x ≈ X' , x')
        → -------------------------
        B ∋ Y x ~ Y' x'            )
      → ----------------------------
      𝒰 n ∋ ty X Y q ~ ty X' Y' q'

    lam :
      (X : ∣ A ∣ )
      (Y : ∥ EA ∥ X → ∣ B ∣)
      (q :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → -----------------------
        B ∋ Y x ~ Y x'           )
      (b : (x : ∥ EA ∥ X) → ∥ EB ∥ (Y x))
      (_ :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → --------------------------
        EB ∋ Y x , b x ≈ Y x' , b x')
      → ---------------------------------
      El n (ty X Y q)

    lamCong :
      (X X' : ∣ A ∣)
      (Y : ∥ EA ∥ X → ∣ B ∣)
      (Y' : ∥ EA ∥ X' → ∣ B ∣)
      (q :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → -----------------------
        B ∋ Y x ~ Y x'           )
      (q' :
        (x x' : ∥ EA ∥ X')
        (_ : EA ∋ X' , x ≈ X' , x')
        → -------------------------
        B ∋ Y' x ~ Y' x'           )
      (b : (x : ∥ EA ∥ X) → ∥ EB ∥ (Y x))
      (b' : (x' : ∥ EA ∥ X') → ∥ EB ∥ (Y' x'))
      (c :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → --------------------------
        EB ∋ Y x , b x ≈ Y x' , b x')
      (c' :
        (x x' : ∥ EA ∥ X')
        (_ : EA ∋ X' , x ≈ X' , x')
        → ------------------------------
        EB ∋ Y' x , b' x ≈ Y' x' , b' x')
      (_ :
        (x : ∥ EA ∥ X)
        (x' : ∥ EA ∥ X')
        (_ : EA ∋ X , x ≈ X' , x')
        → ----------------------------
        EB ∋ Y x , b x ≈ Y' x' , b' x')
      → ---------------------------------------
      ℰ𝓁 n ∋ ty X  Y  q  , lam _ _ _ b  c  ≈
             ty X' Y' q' , lam _ _ _ b' c'

    app :
      (X : ∣ A ∣)
      (Y : ∥ EA ∥ X → ∣ B ∣)
      (q :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → -----------------------
        B ∋ Y x ~ Y x'           )
      (_ : El n (ty X Y q))
      (x : ∥ EA ∥ X)
      → --------------------------
      ∥ EB ∥ (Y x)

    appCong :
      (X X' : ∣ A ∣)
      (Y : ∥ EA ∥ X → ∣ B ∣)
      (Y' : ∥ EA ∥ X' → ∣ B ∣)
      (q :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → -----------------------
        B ∋ Y x ~ Y x'           )
      (q' :
        (x x' : ∥ EA ∥ X')
        (_ : EA ∋ X' , x ≈ X' , x')
        → -------------------------
        B ∋ Y' x ~ Y' x'           )
      (f : El n (ty X Y q))
      (f' : El n (ty X' Y' q'))
      (x : ∥ EA ∥ X)
      (x' : ∥ EA ∥ X')
      (_ : ℰ𝓁 n ∋ ty X Y q , f ≈ ty X' Y' q' , f')
      (_ : EA ∋ X , x ≈ X' , x')
      → ------------------------------------------------
      EB ∋ Y x , app _ _ _ f x ≈ Y' x' , app _ _ _ f' x'

    beta :
      (X : ∣ A ∣)
      (Y : ∥ EA ∥ X → ∣ B ∣)
      (q :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → -----------------------
        B ∋ Y x ~ Y x'           )
      (b : (x : ∥ EA ∥ X) → ∥ EB ∥ (Y x))
      (c :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → --------------------------
        EB ∋ Y x , b x ≈ Y x' , b x')
      (x : ∥ EA ∥ X)
      → ------------------------------------------------
      EB ∋ Y x , app _ _ q (lam _ _ _ b c) x ≈ Y x , b x

    eta :
      (X : ∣ A ∣)
      (Y : ∥ EA ∥ X → ∣ B ∣)
      (q :
        (x x' : ∥ EA ∥ X)
        (_ : EA ∋ X , x ≈ X , x')
        → -----------------------
        B ∋ Y x ~ Y x'           )
      (f : El n (ty X Y q))
      → -------------------------------------------------------
      ℰ𝓁 n ∋
      ty X Y q , lam _ _ _ (app _ _ _ f) (λ _ _ e →
      appCong _ _ _ _ _ _ _ _ _ _ (hrfl (ℰ𝓁 n) (ty X Y q) f) e)
      ≈
      ty X Y q , f

PI≤ :
  {A A' B : Setd}
  {EA : Setd[ A ]}
  {EB : Setd[ B ]}
  {n : ℕ}
  (f : ∣ A' ⟶ A ∣)
  → ------------------------------------
  PI A B EA EB n → PI A' B (f * EA) EB n

PI.ty (PI≤ f p) A = PI.ty p (∣ f ∣ A)
PI.tyCong (PI≤ f p) A A' B B' q q' e =
  PI.tyCong p (∣ f ∣ A) (∣ f ∣ A') B B' q q' (cng f A A' e)
PI.lam (PI≤ f p) A = PI.lam p (∣ f ∣ A)
PI.lamCong (PI≤ f p) A A' = PI.lamCong p (∣ f ∣ A) (∣ f ∣ A')
PI.app (PI≤ f p) A = PI.app p (∣ f ∣ A)
PI.appCong (PI≤ f p) A A' = PI.appCong p (∣ f ∣ A) (∣ f ∣ A')
PI.beta (PI≤ f p) A = PI.beta p (∣ f ∣ A)
PI.eta (PI≤ f p) A = PI.eta p (∣ f ∣ A)

PI≥ :
  {A B B' : Setd}
  {EA : Setd[ A ]}
  {EB : Setd[ B ]}
  {m : ℕ}
  (g : ∣ B' ⟶ B ∣)
  → ------------------------------------
  PI A B EA EB m → PI A B' EA (g * EB) m

PI.ty (PI≥ g p) A B q =
  PI.ty p A (∣ g ∣ ∘ B)
  (λ x x' e → cng g (B x) (B x') (q x x' e))
PI.tyCong (PI≥ g p) A A' B B' q q' r s =
  PI.tyCong p A A' (∣ g ∣ ∘ B) (∣ g ∣ ∘ B')
  (λ x x' e → cng g (B x) (B x') (q x x' e))
  (λ x x' e → cng g (B' x) (B' x') (q' x x' e)) r
  (λ x x' e → cng g (B x) (B' x') (s x x' e))
PI.lam (PI≥ g p) A B q =
  PI.lam p A (∣ g ∣ ∘ B)
  (λ x x' e → cng g (B x) (B x') (q x x' e))
PI.lamCong (PI≥ g p) A A' B B' q q' =
  PI.lamCong p A A' (∣ g ∣ ∘ B) (∣ g ∣ ∘ B')
  (λ x x' e → cng g (B x) (B x') (q x x' e))
  (λ x x' e → cng g (B' x) (B' x') (q' x x' e))
PI.app (PI≥ g p) A B q =
  PI.app p A (∣ g ∣ ∘ B)
  (λ x x' e → cng g (B x) (B x') (q x x' e))
PI.appCong (PI≥ g p) A A' B B' q q' =
  PI.appCong p A A' (∣ g ∣ ∘ B) (∣ g ∣ ∘ B')
  (λ x x' e → cng g (B x) (B x') (q x x' e))
  (λ x x' e → cng g (B' x) (B' x') (q' x x' e))
PI.beta (PI≥ g p) A B q =
  PI.beta p A (∣ g ∣ ∘ B)
  (λ x x' e → cng g (B x) (B x') (q x x' e))
PI.eta (PI≥ g p) A B q =
  PI.eta p A (∣ g ∣ ∘ B)
  (λ x x' e → cng g (B x) (B x') (q x x' e))

----------------------------------------------------------------------
-- Pi-types in each universe
----------------------------------------------------------------------
pi₌ : ∀ n → PI (𝒰 n) (𝒰 n) (ℰ𝓁 n) (ℰ𝓁 n) n

PI.ty (pi₌ 0) = Pi₀
PI.tyCong (pi₌ 0) _ _ _ _ _ _ r r' = (r , r')
PI.lam (pi₌ 0) _ _ _ b e = (b , e)
PI.lamCong (pi₌ 0) _ _ _ _ _ _ _ _ _ _ = id
PI.app (pi₌ 0) _ _ _ (b , _) a = b a
PI.appCong (pi₌ 0) _ _ _ _ _ _ _ _ _ _ b = b _ _
PI.beta (pi₌ 0) _ Y _ b _ a = hrfl (ℰ𝓁 0) (Y a) (b a)
PI.eta (pi₌ 0) _ _ _ (_ , e) = e
PI.ty (pi₌ (1+ _)) = Pi₊
PI.tyCong (pi₌ (1+ _)) _ _ _ _ _ _ r r' = (r , r')
PI.lam (pi₌ (1+ _)) _ _ _ b e = (b , e)
PI.lamCong (pi₌ (1+ _)) _ _ _ _ _ _ _ _ _ _ = id
PI.app (pi₌ (1+ _)) _ _ _ (b , _) a = b a
PI.appCong (pi₌ (1+ _)) _ _ _ _ _ _ _ _ _ _ b = b _ _
PI.beta (pi₌ (1+ n)) _ Y _ b _ a = hrfl (ℰ𝓁 (1+ n)) (Y a) (b a)
PI.eta (pi₌ (1+ _)) _ _ _ (_ , e) = e

----------------------------------------------------------------------
-- Agda-style Pi-types
----------------------------------------------------------------------
pi≤ : ∀{m n} → n ≥ m → PI (𝒰 m) (𝒰 n) (ℰ𝓁 m) (ℰ𝓁 n) (max m n)
pi≤ p
  rewrite Lftsℰ𝓁 p
  | max≤ (≥→≤ p) = PI≤ (Lfts p) (pi₌ _)

pi≥ : ∀{m n} → m ≥ n → PI (𝒰 m) (𝒰 n) (ℰ𝓁 m) (ℰ𝓁 n) (max m n)
pi≥ p
  rewrite Lftsℰ𝓁 p
  | max≥ (≥→≤ p) = PI≥ (Lfts p) (pi₌ _)

pi : ∀ m n → PI (𝒰 m) (𝒰 n) (ℰ𝓁 m) (ℰ𝓁 n) (max m n)
pi m n = ∨elim pi≤ pi≥ (≥total m n)
