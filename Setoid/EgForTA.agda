module Setoid.EgForTA where

open import Prelude

open import Setoid.Definition
open import Setoid.Display

----------------------------------------------------------------------
-- Base setoid universe
----------------------------------------------------------------------
module Universe₀ where
  {- An inductive recursive-recursive-recursive definition of U₀,
  El₀, _~₀_ and _,_≈₀_,_ -}

  infix 3 _~₀_ _,_≈₀_,_

  data U₀ : Set
  El₀ : U₀ → Set
  _~₀_ : U₀ → U₀ → Set
  _,_≈₀_,_ : (A : U₀) → El₀ A → (B : U₀) → El₀ B → Set

  data U₀ where
    Pi₀ :
      (A : U₀)
      (B : El₀ A → U₀)
      (q : ∀ a a' → A , a ≈₀ A , a' → B a ~₀ B a')
      → ------------------------------------------
      U₀
    Unit : U₀
    Nat : U₀

  El₀ (Pi₀ A B x) =
    ∑[ f ∈ ((a : El₀ A) → El₀ (B a)) ]
    (∀ a a' → A , a ≈₀ A , a' → B a , f a ≈₀ B a' , f a')
  El₀ Unit = ⊤
  El₀ Nat = ℕ

  (Pi₀ A B _) ~₀ (Pi₀ A' B' _) =
    (A ~₀ A') ×
    (∀ a a' → A , a ≈₀ A' , a' → B a ~₀ B' a')
  (Pi₀ _ _ _) ~₀ Unit = Ø
  (Pi₀ _ _ _) ~₀ Nat = Ø
  Unit ~₀ (Pi₀ _ _ _) = Ø
  Unit ~₀ Unit = ⊤
  Unit ~₀ Nat = Ø
  Nat ~₀ (Pi₀ _ _ _) = Ø
  Nat ~₀ Unit = Ø
  Nat ~₀ Nat = ⊤

  (Pi₀ A B _) , (f , _) ≈₀ (Pi₀ A' B' _) , (f' , _) =
    ∀ a a' → A , a ≈₀ A' , a' → B a , f a ≈₀ B' a' , f' a'
  (Pi₀ _ _ _) , _ ≈₀ Unit , _ = Ø
  (Pi₀ _ _ _) , _ ≈₀ Nat , _ = Ø
  Unit , _ ≈₀ (Pi₀ _ _ _) , _ = Ø
  Unit , _ ≈₀ Unit , _ = ⊤
  Unit , _ ≈₀ Nat , _ = Ø
  Nat , _ ≈₀ (Pi₀ _ _ _) , _ = Ø
  Nat , _ ≈₀ Unit , _ = Ø
  Nat , a ≈₀ Nat , a' = a ≡ a'

  -- Reflexivity
  rfl₀ :
    (A : U₀)
    → ------
    A ~₀ A
  hrfl₀ :
    (A : U₀)
    (a : El₀ A)
    → ------------
    A , a ≈₀ A , a


rfl₀ (Pi₀ A _ e) = (rfl₀ A , e)
  rfl₀ Unit = tt
  rfl₀ Nat = tt

  hrfl₀ (Pi₀ _ _ _) (_ , e) = e
  hrfl₀ Unit _ = tt
  hrfl₀ Nat _ = refl

  -- Symmetry
  sym₀ :
    {A A' : U₀}
    (_ : A ~₀ A')
    → -----------
    A' ~₀ A
  hsym₀ :
    {A A' : U₀}
    {a : El₀ A}
    {a' : El₀ A'}
    (_ : A ~₀ A')
    (_ : A , a ≈₀ A' , a')
    → --------------------
    A' , a' ≈₀ A , a

  sym₀{Pi₀ _ _ _}{Pi₀ _ _ _} (e , f) =
    sym₀ e , λ a a' e' → sym₀ (f a' a (hsym₀ (sym₀ e) e'))
  sym₀{Unit}{Unit} _ = tt
  sym₀{Nat}{Nat} _ = tt

  hsym₀{Pi₀ _ _ _}{Pi₀ _ _ _} (f , f') g b b' e =
    let s = hsym₀ (sym₀ f) e in
    hsym₀ (f' b' b s) (g b' b s)
  hsym₀{Unit}{Unit} _ _ = tt
  hsym₀{Nat}{Nat} _ refl = refl

  -- Transitivity and coherent coercion
  trs₀ :
    {A A' A'' : U₀}
    (_ : A ~₀ A')
    (_ : A' ~₀ A'')
    → --------------
    A ~₀ A''
  htrs₀ :
    {A A' A'' : U₀}
    {a : El₀ A}
    {a' : El₀ A'}
    {a'' : El₀ A''}
    (_ : A ~₀ A')
    (_ : A' ~₀ A'')
    (_ : A , a ≈₀ A' , a')
    (_ : A' , a' ≈₀ A'' , a'')
    → ------------------------
    A , a ≈₀ A'' , a''
  coe₀ :
    {A A' : U₀}
    (_ : A ~₀ A')
    → ------------
    El₀ A → El₀ A'
  coh₀ :
    {A A' : U₀}
    (q : A ~₀ A')
    (a : El₀ A)
    → ----------------------
    A , a ≈₀ A' , (coe₀ q a)

  trs₀{Pi₀ _ _ _}{Pi₀ _ _ _}{Pi₀ _ _ _} (e , f) (e' , f') =
    (trs₀ e e' , (λ a a'' r →
      let
        a' = coe₀ e a
        r' = coh₀ e a
      in trs₀ (f a a' r') (f' a' a'' (htrs₀
        (sym₀ e) (trs₀ e e') (hsym₀ e r') r))))
  trs₀{Unit}{Unit}{Unit} _ _ = tt
  trs₀{Nat}{Nat}{Nat} _ _ = tt

  htrs₀{Pi₀ _ _ _}{Pi₀ _ _ _}{Pi₀ _ _ _}
    (e , f) (e' , f') g g' a a'' r =
    let
      a'  = coe₀ e a
      r'  = coh₀ e a
      r'' = htrs₀ (sym₀ e) (trs₀ e e') (hsym₀ e r') r
    in htrs₀ (f a a' r') (f' a' a'' r'') (g a a' r') (g' a' a'' r'')
  htrs₀{Unit}{Unit}{Unit} _ _ _ _ = tt
  htrs₀{Nat}{Nat}{Nat} _ _ refl refl = refl

  coe₀{Pi₀ _ _ e}{Pi₀ _ _ _} (e₁ , e₂) (f₁ , f₂) =
    let
      e₁' = sym₀ e₁
    in
    (λ a → let a₁ = coe₀ e₁' a in coe₀
      (e₂ a₁ a (hsym₀ e₁' (coh₀ e₁' a)))
      (f₁ a₁))
    ,
    (λ a a' r →
      let
        a₁    = coe₀ e₁' a
        a₁'   = coe₀ e₁' a'
        r₁    = hsym₀ e₁' (coh₀ e₁' a)
        r₁'   = hsym₀ e₁' (coh₀ e₁' a')
        a₁a₁' = htrs₀ e₁ e₁' r₁ (htrs₀ (rfl₀ _) e₁' r (coh₀ e₁' a'))
        b     = coe₀ (e₂ a₁ a r₁) (f₁ a₁)
        b'    = coe₀ (e₂ a₁' a' r₁') (f₁ a₁')
      in htrs₀ (sym₀ (e₂ a₁ a r₁))
        (e₂ a₁ a' (htrs₀ e₁ (rfl₀ _) r₁ r))
        (hsym₀ (e₂ a₁ a r₁) (coh₀ (e₂ a₁ a r₁) (f₁ a₁)))
        (htrs₀ (e a₁ a₁' a₁a₁') (e₂ a₁' a' r₁') (f₂ a₁ a₁' a₁a₁')
          (coh₀ (e₂ a₁' a' r₁') (f₁ a₁'))))
  coe₀ {Unit} {Unit} _ _ = tt
  coe₀{Nat}{Nat} _ a = a

  coh₀{Pi₀ _ _ e}{Pi₀ _ _ _} (e₁ , e₂) (f₁ , f₂) a a' r =
    let
      e₁'   = sym₀ e₁
      a''   = coe₀ e₁' a'
      r''   = coh₀ e₁' a'
      aa''  = htrs₀ e₁ e₁' r r''
      a''a' = hsym₀ e₁' r''
      b     = coe₀ (e₂ a'' a' a''a') (f₁ a'')
      s     = coh₀ (e₂ a'' a' a''a') (f₁ a'')
    in htrs₀ (e a a'' aa'') (e₂ a'' a' a''a') (f₂ a a'' aa'') s
  coh₀ {Unit} {Unit} _ _ = tt
  coh₀{Nat}{Nat} _ _ = refl

  -- The zeroth setoid universe
  𝒰₀ : Setd

  ∣ 𝒰₀ ∣ = U₀
  𝒰₀ ∋ A ~ B = A ~₀ B
  rfl 𝒰₀ = rfl₀
  sym 𝒰₀ = sym₀
  trs 𝒰₀ = trs₀

  -- The generic family over 𝒰₀
  ℰ𝓁₀ : Setd[ 𝒰₀ ]

  ∥ ℰ𝓁₀ ∥ = El₀
  (ℰ𝓁₀ ∋ A , a ≈ B , b) = A , a ≈₀ B , b
  hrfl ℰ𝓁₀ = hrfl₀
  hsym ℰ𝓁₀ = hsym₀
  htrs ℰ𝓁₀ = htrs₀
  coe ℰ𝓁₀ = coe₀
  coh ℰ𝓁₀ = coh₀

open Universe₀ public

----------------------------------------------------------------------
-- The second universe
----------------------------------------------------------------------
module Universe₁ where
  data U₁ : Set
  El₁ : U₁ → Set
  _~₁_ : U₁ → U₁ → Set
  _,_≈₁_,_ : (A : U₁) → El₁ A → (B : U₁) → El₁ B → Set

  data U₁ where
    Univ : U₁
    Lft :
      (A : ∣ 𝒰₀ ∣)
      → ----------
      U₁
    Pi₁ :
      (A : U₁)
      (B : El₁ A → U₁)
      (q :
        (a a' : El₁ A)
        (_ : A , a ≈₁ A , a')
        → -------------------
        B a ~₁ B a'          )
      → ----------------------
      U₁

  El₁ Univ = ∣ 𝒰₀ ∣
  El₁ (Lft A) = ∥ ℰ𝓁₀ ∥ A
  El₁ (Pi₁ A B x) =
    ∑[ f ∈ ((a : El₁ A) → El₁ (B a)) ]
    (∀ a a' → A , a ≈₁ A , a' → B a , f a ≈₁ B a' , f a')

  Univ ~₁ Univ = ⊤
  Univ ~₁ Lft _ = Ø
  Univ ~₁ Pi₁ _ _ _ = Ø
  Lft A ~₁ Univ = Ø
  Lft A ~₁ Lft A' = 𝒰₀ ∋ A ~ A'
  Lft A ~₁ Pi₁ _ _ _ = Ø
  Pi₁ _ _ _ ~₁ Univ = Ø
  Pi₁ _ _ _ ~₁ Lft _ = Ø
  Pi₁ A B _ ~₁ Pi₁ A' B' _ =
    (A ~₁ A') × (∀ a a' → A , a ≈₁ A' , a' → B a ~₁ B' a')

  Univ , A ≈₁ Univ , A' = 𝒰₀ ∋ A ~ A'
  Univ , _ ≈₁ (Lft _) , _ = Ø
  Univ , _ ≈₁ (Pi₁ _ _ _) , _ = Ø
  (Lft _) , A ≈₁ Univ , _ = Ø
  (Lft A) , x ≈₁ (Lft A') , x' = ℰ𝓁₀ ∋ A , x ≈ A' , x'
  (Lft _) , _ ≈₁ (Pi₁ _ _ _) , _ = Ø
  (Pi₁ _ _ _) , _ ≈₁ Univ , _ = Ø
  (Pi₁ _ _ _) , _ ≈₁ (Lft _) , _ = Ø
  (Pi₁ A B _) , (f , _) ≈₁ (Pi₁ A' B' _) , (f' , _) =
    ∀ a a' → A , a ≈₁ A' , a' → B a , f a ≈₁ B' a' , f' a'

  -- Reflexivity
  rfl₁ :
    (A : U₁)
    → ------
    A ~₁ A
  hrfl₁ :
    (A : U₁)
    (a : El₁ A)
    → ------------
    A , a ≈₁ A , a

  rfl₁ Univ = tt
  rfl₁ (Lft A) = rfl 𝒰₀ A
  rfl₁ (Pi₁ A B q) = (rfl₁ A , q)

  hrfl₁ Univ = rfl 𝒰₀
  hrfl₁ (Lft A) = hrfl ℰ𝓁₀ A
  hrfl₁ (Pi₁ _ _ _) (_ , e) = e

  -- Symmetry
  sym₁ :
    {A A' : U₁}
    (_ : A ~₁ A')
    → ------------
    A' ~₁ A
  hsym₁ :
    {A A' : U₁}
    {a : El₁ A}
    {a' : El₁ A'} →
    (_ : A ~₁ A')
    (_ : A , a ≈₁ A' , a')
    → --------------------
    A' , a' ≈₁ A , a

  sym₁{Univ}{Univ} _ = tt
  sym₁{Lft _}{Lft _} = sym 𝒰₀
  sym₁{Pi₁ A B _}{Pi₁ A' B' _} (e , f) =
    (sym₁{A} e , λ a a' e' →
      sym₁{B a'} (f a' a (hsym₁{A'} (sym₁{A} e) e')))

  hsym₁{Univ}{Univ} _ = sym 𝒰₀
  hsym₁{Lft _}{Lft _} = hsym ℰ𝓁₀
  hsym₁{Pi₁ A B _}{Pi₁ A' B' _} (f , f') g a' a e' =
    let s = hsym₁{A'} (sym₁{A} f) e' in
    hsym₁{B a}{B' a'} (f' a a' s) (g a a' s)


  -- Transitivity and coherent coercion
  trs₁ :
    {A A' A'' : U₁}
    (_ : A ~₁ A')
    (_ : A' ~₁ A'')
    → --------------
    A ~₁ A''
  htrs₁ :
    {A A' A'' : U₁}
    {a : El₁ A}
    {a' : El₁ A'}
    {a'' : El₁ A''}
    (_ : A ~₁ A')
    (_ : A' ~₁ A'')
    (_ : A , a ≈₁ A' , a')
    (_ : A' , a' ≈₁ A'' , a'')
    → ------------------------
    A , a ≈₁ A'' , a''
  coe₁ :
    {A A' : U₁}
    (_ : A ~₁ A')
    → --------------
    El₁ A → El₁ A'
  coh₁ :
    {A A' : U₁}
    (q : A ~₁ A')
    (a : El₁ A)
    → ---------------------------
    A , a ≈₁ A' , coe₁{A}{A'} q a

  trs₁{Univ}{Univ}{Univ} _ _ = tt
  trs₁{Lft _}{Lft _}{Lft _} = trs 𝒰₀
  trs₁{Pi₁ A B _}{Pi₁ A' B' _}{Pi₁ A'' B'' _} (e , f) (e' , f') =
    (trs₁{A} e e' , λ a a'' r →
      let
        a' = coe₁{A} e a
        r' = coh₁{A} e a
      in trs₁{B a}{B' a'}{B'' a''}
        (f a a' r')
        (f' a' a''
          (htrs₁{A'}
            (sym₁{A} e)
            (trs₁{A} e e')
            (hsym₁{A} e r')
            r)))

  htrs₁{Univ}{Univ}{Univ} _ _ = trs 𝒰₀
  htrs₁{Lft _}{Lft _}{Lft _} = htrs ℰ𝓁₀
  htrs₁{Pi₁ A B _}{Pi₁ A' B' _}{Pi₁ A'' B'' _}
    (e , f) (e' , f') g g' a a'' r =
    let
      a'  = coe₁{A} e a
      r'  = coh₁{A} e a
      r'' = htrs₁{A'}
            (sym₁{A} e)
            (trs₁{A} e e')
            (hsym₁{A} e r') r
    in htrs₁{B a}
      (f a a' r')
      (f' a' a'' r'')
      (g a a' r')
      (g' a' a'' r'')

  coe₁{Univ}{Univ} _ a = a
  coe₁{Lft _}{Lft _} = coe ℰ𝓁₀
  coe₁{Pi₁ A B e}{Pi₁ A' B' _} (e₁ , e₂) (f₁ , f₂) =
    let
      e₁' = sym₁{A} e₁
    in
    (λ a → let a₁ = coe₁{A'} e₁' a in coe₁{B a₁}
      (e₂ a₁ a (hsym₁{A'} e₁' (coh₁{A'} e₁' a)))
      (f₁ a₁))
    ,
    (λ a a' r →
      let
        a₁    = coe₁{A'} e₁' a
        a₁'   = coe₁{A'} e₁' a'
        r₁    = hsym₁{A'} e₁' (coh₁{A'} e₁' a)
        r₁'   = hsym₁{A'} e₁' (coh₁{A'} e₁' a')
        a₁a₁' = htrs₁{A} e₁ e₁' r₁
                (htrs₁{A'} (rfl₁ A') e₁' r (coh₁{A'} e₁' a'))
        b     = coe₁{B a₁} (e₂ a₁ a r₁) (f₁ a₁)
        b'    = coe₁{B a₁'} (e₂ a₁' a' r₁') (f₁ a₁')
      in htrs₁{B' a}{B a₁}{B' a'}{b}{f₁ a₁}
         (sym₁{B a₁} (e₂ a₁ a r₁))
         (e₂ a₁ a' (htrs₁{A} e₁ (rfl₁ A') r₁ r))
         (hsym₁{B a₁}
           (e₂ a₁ a r₁)
           (coh₁{B a₁} (e₂ a₁ a r₁) (f₁ a₁)))
         (htrs₁{B a₁}
           (e a₁ a₁' a₁a₁')
           (e₂ a₁' a' r₁')
           (f₂ a₁ a₁' a₁a₁')
           (coh₁{B a₁'} (e₂ a₁' a' r₁') (f₁ a₁'))))

  coh₁{Univ}{Univ} _ a = rfl 𝒰₀ a
  coh₁{Lft _}{Lft _} = coh ℰ𝓁₀
  coh₁{Pi₁ A B e}{Pi₁ A' _ _} (e₁ , e₂) (f₁ , f₂) a a' r =
    let
      e₁'   = sym₁{A} e₁
      a''   = coe₁{A'} e₁' a'
      r''   = coh₁{A'} e₁' a'
      aa''  = htrs₁{A} e₁ e₁' r r''
      a''a' = hsym₁{A'} e₁' r''
      b     = coe₁{B a''} (e₂ a'' a' a''a') (f₁ a'')
      s     = coh₁{B a''} (e₂ a'' a' a''a') (f₁ a'')
    in htrs₁{B a}
      (e a a'' aa'')
      (e₂ a'' a' a''a')
      (f₂ a a'' aa'')
      s

  -- Second universe
  𝒰₁ : Setd
  ∣ 𝒰₁ ∣ = U₁
  _∋_~_ 𝒰₁ = _~₁_
  rfl 𝒰₁ = rfl₁
  sym 𝒰₁ {A} = sym₁ {A}
  trs 𝒰₁ {A} = trs₁ {A}

  ℰ𝓁₁ : Setd[ 𝒰₁ ]
  ∥ ℰ𝓁₁ ∥ = El₁
  (ℰ𝓁₁ ∋ A , a ≈ B , b) = A , a ≈₁ B , b
  hrfl ℰ𝓁₁ = hrfl₁
  hsym ℰ𝓁₁ {A} = hsym₁ {A}
  htrs ℰ𝓁₁ {A} = htrs₁ {A}
  coe  ℰ𝓁₁ {A} = coe₁  {A}
  coh  ℰ𝓁₁ {A} = coh₁  {A}

open Universe₁ public

----------------------------------------------------------------------
-- Embedding
----------------------------------------------------------------------
embed : ∣ 𝒰₀ ∣ → ∣ 𝒰₁ ∣

embed = Lft

lift-el : (A : U₀) → El₀ A → El₁ (embed A)

lift-el _ a = a

retract : (A : U₀) → El₁ (embed A) → El₀ A

retract A a = a

retract-lift : (A : U₀) (a : El₀ A) → retract A (lift-el A a) ≡ a

retract-lift A a = refl
