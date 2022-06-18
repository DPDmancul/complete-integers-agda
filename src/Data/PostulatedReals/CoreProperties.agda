
-- (c) Davide Peressoni 2022

{-# OPTIONS --without-K #-}

--------------------------------
-- Properteis of real numbers --
--------------------------------


module Data.PostulatedReals.CoreProperties where

  open import Data.PostulatedReals.Core
  open import Data.PostulatedReals.Ring public
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import Data.N hiding (_<_ ; _≤_ ; _>_ ; _≥_ ; NonZero ; ≢-nonZero)
  open ℕ
  import Data.Nat.Properties as ℕp
  open import Data.Empty
  open import Data.Sum
  open import Utils
  open import Function.Base
  open import Ops

  +-assoc-middle : (a b c d : ℝ) → (a + b) + (c + d) ≡ a + (b + c) + d
  +-assoc-middle = •-assoc-middle _+_ +-assoc

  +-comm-middle : (a b c d : ℝ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +-comm-middle = •-comm-middle _+_ +-comm +-assoc-middle

  *-assoc-middle : (a b c d : ℝ) → (a · b) · (c · d) ≡ a · (b · c) · d
  *-assoc-middle = •-assoc-middle _·_ *-assoc

  *-comm-middle : (a b c d : ℝ) → (a · b) · (c · d) ≡ (a · c) · (b · d)
  *-comm-middle = •-comm-middle _·_ *-comm *-assoc-middle

  -1² : -1ℝ · -1ℝ ≡ unit
  -1² rewrite -‿*-distribʳ -1ℝ 1ℝ | *-identityʳ -1ℝ = -‿involutive unit

  *-cancel-neg : (x y : ℝ) → - x · - y ≡ x · y
  *-cancel-neg x y rewrite sym (*-neg-identityˡ x) | sym (*-neg-identityˡ y)
    | *-comm-middle -1ℝ x -1ℝ y | -1² = *-identityˡ (x · y)

  postulate
    *-inverseʳ : (x : ℝ) → .⦃ _ : NonZero x ⦄ → x · x ⁻¹ ≡ unit

  *-inverseˡ : (x : ℝ) → .⦃ _ : NonZero x ⦄ → x ⁻¹ · x ≡ unit
  *-inverseˡ x rewrite *-comm (x ⁻¹) x = *-inverseʳ x

  1⁻¹ : unit ⁻¹ ≡ unit
  1⁻¹ rewrite sym $ *-identityˡ (unit ⁻¹) = *-inverseʳ unit

  x·y≡0 : (x y : ℝ) → x · y ≡ 0ℝ → x ≡ 0ℝ ⊎ y ≡ 0ℝ
  x·y≡0 x y p with isZero x
  ... | inj₁ x≡0 = inj₁ x≡0
  ... | inj₂ q   with isZero y
  ... | inj₁ y≡0 = inj₂ y≡0
  ... | inj₂ r   = helper $ r $ begin
      y                ≡˘⟨ *-identityˡ y ⟩
      1ℝ · y           ≡˘⟨ cong (_· y) (*-inverseʳ x) ⟩
      (x / x) · y     ≡⟨ *-assoc x (x ⁻¹) y ⟩
      x · (x ⁻¹ · y)  ≡⟨ cong (_·_ x) (*-comm (x ⁻¹) y) ⟩
      x · (y · x ⁻¹)  ≡˘⟨ *-assoc x y (x ⁻¹) ⟩
      x · y · x ⁻¹    ≡⟨ cong (_· x ⁻¹) p ⟩
      0ℝ · x ⁻¹       ≡⟨ zeroˡ (x ⁻¹) ⟩
      0ℝ ∎
    where
    helper : ⊥ → x ≡ 0ℝ ⊎ y ≡ 0ℝ
    helper ()
    instance
      _ = ≢-nonZero q

  x·y≢0 : {x y : ℝ} → x ≢0 → y ≢0 → x · y ≢0
  x·y≢0 {x} {y} p q xy≡0 with x·y≡0 x y xy≡0
  ... | inj₁ x≡0 = p x≡0
  ... | inj₂ y≡0 = q y≡0

  instance
    x·y-nonZero : {x y : ℝ} .⦃ _ : NonZero x ⦄ .⦃ _ : NonZero y ⦄ →
      NonZero (x · y)
    x·y-nonZero ⦃ p ⦄ ⦃ q ⦄ = ≢-nonZero $ x·y≢0 (≢-nonZero⁻¹ p) (≢-nonZero⁻¹ q)

  -x≢0 : {x : ℝ} → x ≢0 → - x ≢0
  -x≢0 {x} p -x≡0 = p $ begin
    x       ≡˘⟨ +-identityʳ x ⟩
    x + 0ℝ  ≡˘⟨ cong (_+_ x) -x≡0 ⟩
    x + - x ≡⟨ -‿inverseʳ x ⟩
    0ℝ ∎

  instance
    -x-nonZero : {x : ℝ} .⦃ _ : NonZero x ⦄ → NonZero (- x)
    -x-nonZero ⦃ p ⦄ = ≢-nonZero $ -x≢0 (≢-nonZero⁻¹ p)

  x⁻¹≢0 : {x : ℝ} → (p : x ≢0) → (x ⁻¹) ⦃ ≢-nonZero p ⦄ ≢0
  x⁻¹≢0 {x} p x⁻¹≡0 = p $ begin
    x            ≡˘⟨ *-identityʳ x ⟩
    x · 1ℝ       ≡˘⟨ cong (_·_ x) (*-inverseʳ x) ⟩
    x · (x / x)  ≡⟨ cong (λ y → x · (x · y)) x⁻¹≡0 ⟩
    x · (x · 0ℝ) ≡⟨ cong (_·_ x) (zeroʳ x) ⟩
    x · 0ℝ       ≡⟨ zeroʳ x ⟩
    0ℝ ∎
    where instance _ = ≢-nonZero p

  instance
    x⁻¹-nonZero : {x : ℝ} .⦃ _ : NonZero x ⦄ → NonZero (x ⁻¹)
    x⁻¹-nonZero ⦃ p ⦄ = ≢-nonZero $ x⁻¹≢0 (≢-nonZero⁻¹ p)

  ⁻¹-distrib-* : (x y : ℝ) → .⦃ p : NonZero x ⦄ → .⦃ q : NonZero y ⦄ →
    ((x · y)⁻¹) ⦃ x·y-nonZero ⦃ p ⦄ ⦃ q ⦄ ⦄ ≡ x ⁻¹ · y ⁻¹
  ⁻¹-distrib-* x y ⦃ p ⦄ ⦃ q ⦄ = sym $ begin
      x ⁻¹ · y ⁻¹       ≡˘⟨ *-identityʳ (x ⁻¹ · y ⁻¹) ⟩
      x ⁻¹ · y ⁻¹ · unit
        ≡˘⟨ cong (_·_ (x ⁻¹ · y ⁻¹)) (*-inverseʳ (x · y) ⦃ _ ⦄) ⟩
      x ⁻¹ · y ⁻¹ · ((x · y) · xy⁻¹)
        ≡˘⟨ *-assoc (x ⁻¹ · y ⁻¹) (x · y) (xy⁻¹) ⟩
      (x ⁻¹ · y ⁻¹ · (x · y)) · xy⁻¹
        ≡⟨ cong (_· xy⁻¹) (*-comm-middle (x ⁻¹) (y ⁻¹) x y) ⟩
      (x ⁻¹ · x) · (y ⁻¹ · y) · xy⁻¹
        ≡⟨ cong₂ (λ a b → a · b · xy⁻¹) (*-inverseˡ x) (*-inverseˡ y) ⟩
      unit · unit · xy⁻¹ ≡⟨ cong (_· xy⁻¹ ) (*-identityˡ unit) ⟩
      unit · xy⁻¹        ≡⟨ *-identityˡ xy⁻¹ ⟩
      xy⁻¹ ∎
      where
        xy⁻¹ = (x · y)⁻¹

  /-mul : (a b c d : ℝ) .⦃ p : NonZero b ⦄ .⦃ q : NonZero d ⦄ →
    a / b · c / d ≡ ((a · c) / (b · d)) ⦃ x·y-nonZero ⦃ p ⦄ ⦃ q ⦄ ⦄
  /-mul a b c d ⦃ p ⦄ ⦃ q ⦄ = begin
      a / b · c / d             ≡⟨ *-comm-middle a (b ⁻¹) c (d ⁻¹) ⟩
      (a · c) · (b ⁻¹ · d ⁻¹)   ≡˘⟨ cong (_·_ (a · c))  (⁻¹-distrib-* b d) ⟩
      ((a · c) / (b · d)) ⦃ _ ⦄ ∎

  x/1 : (x : ℝ) → x / unit ≡ x
  x/1 x rewrite 1⁻¹ = *-identityʳ x

  /-simplˡ : (x y z : ℝ) .⦃ p : NonZero x ⦄ .⦃ q : NonZero z ⦄ →
    ((x · y) / (x · z))  ⦃ x·y-nonZero ⦃ p ⦄ ⦃ q ⦄ ⦄ ≡ y / z
  /-simplˡ x y z ⦃ p ⦄ rewrite sym (/-mul x x y z) | *-inverseʳ x ⦃ p ⦄ =
    *-identityˡ (y / z)

  ⁻¹-cong : {a b : ℝ} .⦃ p : NonZero a ⦄ .⦃ q : NonZero b ⦄ → a ≡ b → a ⁻¹ ≡ b ⁻¹
  ⁻¹-cong refl = refl

  /-cong : {a b c d : ℝ} .⦃ p : NonZero b ⦄ .⦃ q : NonZero d ⦄ → a ≡ c → b ≡ d →
    a / b ≡ c / d
  /-cong refl refl = refl

  /-simplʳ : (x y z : ℝ) .⦃ p : NonZero x ⦄ .⦃ q : NonZero z ⦄ →
    ((y · x) / (z · x)) ⦃ x·y-nonZero ⦃ q ⦄ ⦃ p ⦄ ⦄ ≡ y / z
  /-simplʳ x y z ⦃ p ⦄ ⦃ q ⦄ = begin
    ((y · x) / (z · x)) ⦃ _ ⦄ ≡⟨ /-cong ⦃ _ ⦄ ⦃ _ ⦄ (*-comm y x) (*-comm z x) ⟩
    ((x · y) / (x · z)) ⦃ _ ⦄ ≡⟨ /-simplˡ x y z ⟩
    y / z ∎

  /-coef : (x y z : ℝ) .⦃ p : NonZero z ⦄ → x · y / z ≡ (x · y) / z
  /-coef x y z ⦃ p ⦄ rewrite sym (x/1 x) | /-mul x 1ℝ y z ⦃ 1-nonZero ⦄ ⦃ p ⦄
    | x/1 x | ⁻¹-distrib-* 1ℝ z ⦃ 1-nonZero ⦄ ⦃ p ⦄ | 1⁻¹
    | *-identityˡ (z ⁻¹) = refl

  /-coef-simplˡ : (x y z : ℝ) .⦃ p : NonZero x ⦄ .⦃ q : NonZero z ⦄ →
    x · (y / (x · z)) ⦃ x·y-nonZero ⦃ p ⦄ ⦃ q ⦄ ⦄ ≡ y / z
  /-coef-simplˡ x y z rewrite /-coef x y (x · z) ⦃ _ ⦄ =
    /-simplˡ x y z

  private
    1/1/x-help : (x : ℝ) .⦃ p : NonZero x ⦄ → x · 1ℝ / x ≡ 1ℝ
    1/1/x-help x rewrite /-coef x 1ℝ x ⦃ _ ⦄ | *-identityʳ x =
      *-inverseʳ x

  1/1/x : (x : ℝ) .⦃ p : NonZero x ⦄ → unit / (unit / x) ≡ x
  1/1/x x ⦃ p ⦄ = begin
    1ℝ / (1ℝ / x)      ≡˘⟨ cong (_· (1ℝ / x)⁻¹) (*-inverseʳ x) ⟩
    (x / x) / (1ℝ / x) ≡⟨ /-simplʳ (x ⁻¹) x 1ℝ  ⟩
    x / 1ℝ             ≡⟨ x/1 x ⟩
    x ∎

  -- ------------------
  -- -- Inequalities --
  -- ------------------

  postulate
    ≤-refl : (x : ℝ) → x ≤ x
    ≤-antisym : {x y : ℝ} → x ≤ y → x ≥ y → x ≡ y
    ≤-trans : {x y z : ℝ} → x ≤ y → y ≤ z → x ≤ z
    ≤-total : (x y : ℝ) → x ≤ y ⊎ x ≥ y
    +-monoʳ-≤ : {x y : ℝ} → x ≤ y → (z : ℝ) → x + z ≤ y + z
    *-mono-≥0 : {x y : ℝ} → x ≥ 0ℝ → y ≥ 0ℝ → x · y ≥ 0ℝ

  ≥-neg : {x : ℝ} → x ≥ 0ℝ → - x ≤ 0ℝ
  ≥-neg {x} 0≤x with +-monoʳ-≤ 0≤x (- x)
  ... | 0-x≤x-x rewrite +-identityˡ (- x) | -‿inverseʳ x = 0-x≤x-x

  ≤-neg : {x : ℝ} → x ≤ 0ℝ → - x ≥ 0ℝ
  ≤-neg {x} x≤0 with +-monoʳ-≤ x≤0 (- x)
  ... | x-x≤0-x rewrite +-identityˡ (- x) | -‿inverseʳ x = x-x≤0-x

  *-mono-≤0 : {x y : ℝ} → x ≤ 0ℝ → y ≤ 0ℝ → x · y ≥ 0ℝ
  *-mono-≤0 {x} {y} x≤0 y≤0 rewrite sym (*-cancel-neg x y) =
    *-mono-≥0 (≤-neg x≤0) (≤-neg y≤0)

  *-≤0-≥0 : {x y : ℝ} → x ≤ 0ℝ → y ≥ 0ℝ → x · y ≤ 0ℝ
  *-≤0-≥0 {x} {y} x≤0 y≥0 rewrite sym (-‿involutive (x · y)) | -‿distribˡ-* x y =
   ≥-neg (*-mono-≥0 (≤-neg x≤0) y≥0)

  *-≥0-≤0 : {x y : ℝ} → x ≥ 0ℝ → y ≤ 0ℝ → x · y ≤ 0ℝ
  *-≥0-≤0 {x} {y} x≥0 y≤0 rewrite *-comm x y = *-≤0-≥0 y≤0 x≥0

  -- --------------------
  -- -- Exponent rules --
  -- --------------------

  sum-exp-ℕ : (x : ℝ) → (n m : ℕ) → x ^ (n + m) ≡ x ^ n · x ^ m
  sum-exp-ℕ x zero      m = sym (*-identityˡ (x ^ m))
  sum-exp-ℕ x (ℕ.suc n) m rewrite *-assoc x (x ^ n) (x ^ m) =
    cong (_·_ x) (sum-exp-ℕ x n m)

  mul-base-ℕ : (x y : ℝ) → (n : ℕ) → (x · y) ^ n ≡ x ^ n · y ^ n
  mul-base-ℕ x y 0       = sym (*-identityʳ 1ℝ)
  mul-base-ℕ x y (suc n) rewrite *-comm-middle x (x ^ n) y (y ^ n) =
    cong (_·_ (x · y)) (mul-base-ℕ x y n)

  1^n : (n : ℕ) → 1ℝ ^ n ≡ 1ℝ
  1^n 0       = refl
  1^n (suc n) rewrite 1^n n = *-identityˡ 1ℝ

  double-exp-ℕ : (x : ℝ) → (n m : ℕ) → (x ^ n) ^ m ≡ x ^ (n · m)
  double-exp-ℕ x 0       m = 1^n m
  double-exp-ℕ x (suc n) m rewrite mul-base-ℕ x (x ^ n) m
    | double-exp-ℕ x n m = sym (sum-exp-ℕ x m (n · m))

  x^nm=x^mn : (x : ℝ) → (n m : ℕ) → (x ^ n) ^ m ≡ (x ^ m) ^ n
  x^nm=x^mn x n m rewrite double-exp-ℕ x n m | ℕp.*-comm n m =
    sym (double-exp-ℕ x m n)

