
-- (c) Davide Peressoni 2022

{-# OPTIONS --without-K #-}

--------------------------------
-- Properteis of real numbers --
--------------------------------


module Data.PostulatedReals.Properties where

  open import Data.PostulatedReals
  open import Data.PostulatedReals.CoreProperties public

  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import Data.N hiding (_<_ ; _≤_ ; _>_ ; _≥_ ; NonZero ; ≢-nonZero)
  open ℕ
  import Data.Nat.Properties as ℕp
  open import Data.Int hiding (∣_∣ ; suc ; _<_ ; _≤_ ; _>_ ; _≥_ ; NonZero ; ≢-nonZero)
  open ℤ
  import Data.Int.Properties as ℤp
  -- open import Data.Empty
  open import Data.Sum
  -- open import Data.Product
  -- open import Utils
  open import Function.Base
  open import Ops

  ∣x∣∣x∣ : (x : ℝ) → ∣ x ∣ · ∣ x ∣ ≡ x ^ 2
  ∣x∣∣x∣ x rewrite *-identityʳ x with ≤-total x 0ℝ
  ... | inj₁ x≤0 = *-cancel-neg x x
  ... | inj₂ x≥0 = refl

  ∣x∣² : (x : ℝ) → ∣ x ∣ ^ 2 ≡ x ^ 2
  ∣x∣² x rewrite *-identityʳ ∣ x ∣ = ∣x∣∣x∣ x

  ∣x∣²≢0 : {x : ℝ} → (p : x ≢0) → ∣ x ∣ ^ 2 ≢0
  ∣x∣²≢0 {x} p rewrite *-identityʳ ∣ x ∣ = x·y≢0 q q
    where q = ∣x∣≢0 p

  instance
    ∣x∣²-nonZero : {x : ℝ} .⦃ _ : NonZero x ⦄ → NonZero (∣ x ∣ ^ 2)
    ∣x∣²-nonZero {x} ⦃ p ⦄ = ≢-nonZero $ ∣x∣²≢0 $ ≢-nonZero⁻¹ p

  ∣∣x∣∣ : (x : ℝ) → ∣ ∣ x ∣ ∣ ≡ ∣ x ∣
  ∣∣x∣∣ x  with ≤-total x 0ℝ
  ... | inj₁ x≤0 with ≤-total (- x) 0ℝ
  ... | inj₂ -x≥0 = refl
  ... | inj₁ -x≤0 rewrite ≤-antisym -x≤0 (≤-neg x≤0) = -0#≈0#
  ∣∣x∣∣ x  | inj₂ x≥0 with ≤-total x 0ℝ
  ... | inj₂ x≥0 = refl
  ... | inj₁ x≤0 rewrite ≤-antisym x≤0 x≥0 = -0#≈0#


  ∣x∣∣y∣ : (x y : ℝ) → ∣ x ∣ · ∣ y ∣ ≡ ∣ x · y ∣
  ∣x∣∣y∣ x y with ≤-total x 0ℝ | ≤-total y 0ℝ | ≤-total (x · y) 0ℝ
  ... | inj₁ x≤0 | inj₁ y≤0 | inj₁ xy≤0  rewrite *-cancel-neg x y
    | ≤-antisym xy≤0 (*-mono-≤0 x≤0 y≤0) = sym -0#≈0#
  ... | inj₁ x≤0 | inj₁ y≤0 | inj₂ xy≥0 = *-cancel-neg x y
  ... | inj₁ x≤0 | inj₂ y≥0 | inj₁ xy≤0 = sym (-‿distribˡ-* x y)
  ... | inj₁ x≤0 | inj₂ y≥0 | inj₂ xy≥0 rewrite sym (-‿distribˡ-* x y)
    | ≤-antisym (*-≤0-≥0 x≤0 y≥0) xy≥0 = -0#≈0#
  ... | inj₂ x≥0 | inj₁ y≤0 | inj₁ xy≤0 = sym (-‿distribʳ-* x y)
  ... | inj₂ x≥0 | inj₁ y≤0 | inj₂ xy≥0 rewrite sym (-‿distribʳ-* x y)
    | ≤-antisym (*-≥0-≤0 x≥0 y≤0) xy≥0 = -0#≈0#
  ... | inj₂ x≥0 | inj₂ y≥0 | inj₁ xy≤0 rewrite ≤-antisym xy≤0
    (*-mono-≥0 x≥0 y≥0) = sym -0#≈0#
  ... | inj₂ x≥0 | inj₂ y≥0 | inj₂ xy≥0 = refl

  ^-cong : {x y : ℝ} .⦃ _ : NonZero x ⦄ .⦃ _ : NonZero y ⦄ → {z w : ℤ} →
    x ≡ y → z ≡ w → x ^ z ≡ y ^ w
  ^-cong refl refl = refl

  -- --------------------
  -- -- Exponent rules --
  -- --------------------
  private
    sum-exp-help : {x : ℝ} .⦃ _ : NonZero x ⦄ → (n m : ℕ) →
      x ^ (pos n  + -[1+ m ]) ≡ x ^ pos n · x ^ -[1+ m ]
    sum-exp-help {x} ⦃ p ⦄ 0       m = sym $ *-identityˡ (((x ^ suc m)⁻¹) ⦃ _ ⦄)
    sum-exp-help {x} ⦃ p ⦄ (suc n) 0 rewrite /-simplˡ x (x ^ n) 1ℝ ⦃ p ⦄ ⦃ 1-nonZero ⦄
      | 1⁻¹ = sym $ *-identityʳ (x ^ n)
    sum-exp-help {x} ⦃ p ⦄ (suc n) (suc m) rewrite ℤp.[1+m]⊖[1+n]≡m⊖n n (suc m)
      | *-assoc (x ^ n) x (((x ^ suc (suc m))⁻¹) ⦃ x^n-nonZero ⦃ p ⦄ {suc (suc m)} ⦄)
      | /-simplˡ x (x ^ n) (x ^ suc m) ⦃ p ⦄ ⦃ _ ⦄ =
        sum-exp-help n m

  sum-exp : (x : ℝ) .⦃ _ : NonZero x ⦄ → (z w : ℤ) →  x ^ (z + w) ≡ x ^ z · x ^ w
  sum-exp x (pos n)  (pos m)  = sum-exp-ℕ x n m
  sum-exp _ (pos n)  -[1+ m ] = sum-exp-help n m
  sum-exp x -[1+ n ] (pos m)
    rewrite *-comm (((x ^ suc n)⁻¹) ⦃ _ ⦄) (x ^ m) =
    sum-exp-help m n
  sum-exp x -[1+ n ] -[1+ m ] = trans (⁻¹-cong ⦃ _ ⦄ ⦃ _ ⦄ $ help)
    (⁻¹-distrib-* (x ^ suc n) (x ^ suc m) ⦃ _ ⦄ ⦃ _ ⦄)
    where
    help : x ^ suc (suc (n + m)) ≡ x ^ suc n · x ^ suc m
    help = begin
      x ^ suc (suc (n + m)) ≡˘⟨ cong (λ n → x ^ suc n) (ℕp.+-suc n m) ⟩
      x ^ (suc n + suc m)   ≡⟨ sum-exp-ℕ x (suc n) (suc m) ⟩
      x ^ suc n · x ^ suc m ∎

  mul-base : (x y : ℝ) .⦃ p : NonZero x ⦄ .⦃ q : NonZero y ⦄ → (z : ℤ) → let
    r = x·y-nonZero ⦃ p ⦄ ⦃ q ⦄
    in ((x · y) ^ z) ⦃ r ⦄ ≡ x ^ z · y ^ z
  mul-base x y             (pos n)  = mul-base-ℕ x y n
  mul-base x y ⦃ p ⦄ ⦃ q ⦄ -[1+ n ]
    rewrite sym $ ⁻¹-distrib-* (x ^ (suc n)) (y ^ (suc n))
    ⦃ x^n-nonZero ⦃ p ⦄ {suc n} ⦄ ⦃ x^n-nonZero ⦃ q ⦄ {suc n} ⦄ =
    ⁻¹-cong ⦃ x^n-nonZero ⦃ x·y-nonZero ⦃ p ⦄ ⦃ q ⦄ ⦄ {suc n} ⦄ ⦃ _ ⦄ $
      mul-base-ℕ x y (suc n)

  private
    double-exp-help : (x : ℝ) .⦃ p : NonZero x ⦄ → (n m : ℕ) → let
      q = x^n-nonZero ⦃ x^n-nonZero ⦃ p ⦄ {n} ⦄ {suc m}
      in (((x ^ n) ^ suc m)⁻¹) ⦃ q ⦄ ≡ x ^ (pos n · -[1+ m ])
    double-exp-help x       0       m = trans
      (⁻¹-cong ⦃ _ ⦄ $ trans (*-identityˡ (1ℝ ^ m)) (1^n m)) 1⁻¹
    double-exp-help x ⦃ p ⦄ (suc n) m = ⁻¹-cong ⦃ _ ⦄
      ⦃ x^n-nonZero ⦃ p ⦄ {suc n · suc m} ⦄ $ double-exp-ℕ x (suc n) (suc m)

  x^z≢0 : {x : ℝ} → (p : x ≢0) → (z : ℤ) → (x ^ z) ⦃ ≢-nonZero p ⦄ ≢0
  x^z≢0 {x} p (pos n)  = x^n≢0 p n
  x^z≢0 {x} p -[1+ n ] = x⁻¹≢0 $ x^n≢0 p (suc n)

  instance
    x^z-nonZero : {x : ℝ} .⦃ _ : NonZero x ⦄ → {z : ℤ} → NonZero (x ^ z)
    x^z-nonZero ⦃ p ⦄ {z} = ≢-nonZero $ x^z≢0 (≢-nonZero⁻¹ p) z

  mutual
    [1/x]^n : (x : ℝ) .⦃ p : NonZero x ⦄ → (n : ℕ) →
      (x ⁻¹) ^ n ≡ ((x ^ n)⁻¹) ⦃ x^n-nonZero ⦃ p ⦄ {n} ⦄
    [1/x]^n x ⦃ p ⦄ n = begin
      (x ⁻¹) ^ n
        ≡˘⟨ (cong (_^ n) $ ⁻¹-cong ⦃ _ ⦄ $ *-identityʳ x) ⟩
      ((x ^ -[1+ 0 ]) ^ pos n) ⦃ q ⦄
        ≡⟨ helper n ⟩
      x ^ (-[1+ 0 ] · pos n)
        ≡⟨ cong (λ y → (x ^ y) ⦃ _ ⦄) (ℤp.*-comm -[1+ 0 ] (pos n)) ⟩
      x ^ (pos n · -[1+ 0 ]) ≡˘⟨ double-exp x (pos n) -[1+ 0 ] ⟩
      ((x ^ n) ^ -[1+ 0 ]) ⦃ r ⦄
        ≡⟨ (⁻¹-cong ⦃ _ ⦄ ⦃ r ⦄ $ *-identityʳ (x ^ n)) ⟩
      ((x ^ n)⁻¹) ⦃ _ ⦄ ∎
      where
        instance
          q = x^z-nonZero ⦃ p ⦄ { -[1+ 0 ]}
          r = x^n-nonZero ⦃ p ⦄ {n}
          s = x·y-nonZero ⦃ p ⦄ ⦃ 1-nonZero ⦄
        helper : (n : ℕ) → ((x · 1ℝ)⁻¹) ⦃ s ⦄ ^ n ≡ x ^ (-[1+ 0 ] · pos n)
        helper 0       = refl
        helper (suc n) rewrite helper n | ⁻¹-cong ⦃ x·y-nonZero ⦄ $ *-identityʳ x
          | ⁻¹-distrib-* x (x ^ (n + 0)) ⦃ p ⦄ ⦃ x^n-nonZero ⦃ p ⦄ {n + 0} ⦄
          with n
        ... | 0     = cong (_·_ (x ⁻¹)) $  sym $ 1⁻¹
        ... | suc n = refl

    double-exp : (x : ℝ) .⦃ p : NonZero x ⦄ → (z w : ℤ) → let
      q = x^z-nonZero ⦃ p ⦄ {z}
      in ((x ^ z) ^ w) ⦃ q ⦄ ≡ x ^ (z · w)
    double-exp x       (pos n)  (pos m)  rewrite ℤp.pos-mul n m =
      double-exp-ℕ x n m
    double-exp x       (pos n)  -[1+ m ] = double-exp-help x n m
    double-exp x ⦃ p ⦄ -[1+ n ] (pos 0)  rewrite ℤp.*-comm -[1+ n ] 0ℤ = refl
    double-exp x ⦃ p ⦄ -[1+ n ] +[1+ m ]
      rewrite [1/x]^n (x ^ suc n) ⦃ x^n-nonZero ⦃ p ⦄ {suc n} ⦄ (suc m) =
        ⁻¹-cong ⦃ _ ⦄ ⦃ _ ⦄ $ trans
        (cong (_·_ (x ^ suc n)) $ double-exp-ℕ x (suc n) m)
        (trans (sym $ sum-exp-ℕ x (suc n) (m + (n · m)))
               (cong (λ n → x ^ suc n) $ begin
                 n + (m + n · m) ≡˘⟨ ℕp.+-assoc n m (n · m) ⟩
                 (n + m) + n · m ≡⟨ (cong (_+ n · m) $ ℕp.+-comm n m) ⟩
                 (m + n) + n · m ≡⟨ ℕp.+-assoc m n (n · m) ⟩
                 m + (n + n · m) ≡˘⟨ cong (_+_ m) (ℕp.*-suc n m) ⟩
                 m + n · suc m ∎) )
    double-exp x ⦃ p ⦄ -[1+ n ] -[1+ m ] = begin
      (((((x ^ suc n) ⁻¹) ⦃ q ⦄) ^ (suc m))⁻¹) ⦃ _ ⦄
        ≡⟨ ⁻¹-cong ⦃ _ ⦄ ⦃ _ ⦄ $ [1/x]^n  (x ^ suc n) ⦃ _ ⦄ (suc m) ⟩
      ((((x ^ suc n) ^ (suc m))⁻¹) ⦃ _ ⦄ ⁻¹) ⦃ t ⦄
        ≡⟨ ⁻¹-involutive ((x ^ suc n) ^ suc m) ⦃ s ⦄ ⟩
      (x ^ suc n) ^ (suc m) ≡⟨ double-exp-ℕ x (suc n) (suc m) ⟩
      x ^ (suc n · suc m) ∎
      where
      q = x^n-nonZero ⦃ p ⦄ {suc n}
      r = x⁻¹-nonZero ⦃ q ⦄
      s = x^n-nonZero ⦃ q ⦄ {suc m}
      t = x⁻¹-nonZero ⦃ s ⦄

  ∣x∣^2z : (x : ℝ) .⦃ p : NonZero x ⦄ → (z : ℤ) → ∣ x ∣ ^ (2ℤ · z) ≡ x ^ (2ℤ · z)
  ∣x∣^2z x ⦃ p ⦄ z = begin
    ∣ x ∣ ^ (2ℤ · z)      ≡˘⟨ double-exp ∣ x ∣ 2ℤ z ⟩
    ((∣ x ∣ ^ 2ℤ) ^ z)    ≡⟨ ^-cong ⦃ ∣x∣²-nonZero ⦃ p ⦄ ⦄ ⦃ _ ⦄ {z} (∣x∣² x) refl ⟩
    ((x ^ 2ℤ) ^ z) ⦃ _ ⦄  ≡⟨ double-exp x 2ℤ z ⟩
    x ^ (2ℤ · z)          ∎

  ∣x^2z∣ : (x : ℝ) .⦃ p : NonZero x ⦄ → (z : ℤ) → ∣ x ^ (2ℤ · z) ∣ ≡ x ^ (2ℤ · z)
  ∣x^2z∣ x ⦃ p ⦄ z rewrite ℤp.*-comm 2ℤ z | sym $ double-exp x z 2ℤ with ≤-total (x ^ z) 0ℝ
  ... | inj₁ x^z≤0 with ≤-total (((x ^ z) ^ 2ℤ) ⦃ x^z-nonZero ⦃ p ⦄ {z} ⦄) 0ℝ
  ... | inj₂ x^2z≥0 = refl
  ... | inj₁ x^2z≤0 rewrite *-identityʳ (x ^ z)
    | ≤-antisym x^2z≤0 (*-mono-≤0 x^z≤0 x^z≤0) = -0#≈0#
  ∣x^2z∣ x ⦃ p ⦄ z  | inj₂ x^z≥0 with ≤-total (((x ^ z) ^ 2ℤ) ⦃ x^z-nonZero ⦃ p ⦄ {z} ⦄) 0ℝ
  ... | inj₂ x^2z≥0 = refl
  ... | inj₁ x^2z≤0 rewrite *-identityʳ (x ^ z)
    | ≤-antisym x^2z≤0 (*-mono-≥0 x^z≥0 x^z≥0) = -0#≈0#
