
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
  open import Data.N hiding (_<_ ; _≤_ ; _>_ ; _≥_)
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
    *-inverseʳ : {x : ℝ} → .(p : x ≢0) → x · (x≢0 x {p}) ⁻¹ ≡ unit

  *-inverseˡ : {x : ℝ} → .(p : x ≢0) → (x≢0 x {p}) ⁻¹ · x ≡ unit
  *-inverseˡ {x} p rewrite *-comm ((x≢0 x {p}) ⁻¹) x = *-inverseʳ p

  1⁻¹ : (x≢0 unit {1≢0})⁻¹ ≡ unit
  1⁻¹ rewrite sym (*-identityˡ ((x≢0 unit {1≢0})⁻¹)) = *-inverseʳ 1≢0

  x·y≡0 : (x y : ℝ) → x · y ≡ 0ℝ → x ≡ 0ℝ ⊎ y ≡ 0ℝ
  x·y≡0 x y p with isZero x
  ... | inj₁ x≡0 = inj₁ x≡0
  ... | inj₂ q   with isZero y
  ... | inj₁ y≡0 = inj₂ y≡0
  ... | inj₂ r   = helper $ r $ begin
    y                ≡˘⟨ *-identityˡ y ⟩
    1ℝ · y           ≡˘⟨ cong (_· y) (*-inverseʳ q) ⟩
    (x / x₀) · y     ≡⟨ *-assoc x (x₀ ⁻¹) y ⟩
    x · (x₀ ⁻¹ · y)  ≡⟨ cong (_·_ x) (*-comm (x₀ ⁻¹) y) ⟩
    x · (y · x₀ ⁻¹)  ≡˘⟨ *-assoc x y (x₀ ⁻¹) ⟩
    x · y · x₀ ⁻¹    ≡⟨ cong (_· x₀ ⁻¹) p ⟩
    0ℝ · x₀ ⁻¹       ≡⟨ zeroˡ (x₀ ⁻¹) ⟩
    0ℝ ∎
    where
    x₀ = x≢0 x {q}
    helper : ⊥ → x ≡ 0ℝ ⊎ y ≡ 0ℝ
    helper ()

  x·y≢0 : {x y : ℝ} → .(x ≢0) → .(y ≢0) → x · y ≢0
  x·y≢0 {x} {y} p q xy≡0 with x·y≡0 x y xy≡0
  ... | inj₁ x≡0 = ⊥-irrelevant (p x≡0)
  ... | inj₂ y≡0 = ⊥-irrelevant (q y≡0)

  private
    ℝ\0≡-help : {x y : ℝ} → x ≢0 → x ≡ y → y ≢0
    ℝ\0≡-help p refl = p

  ℝ\0≡ : {x y : ℝ} → .(p : x ≢0) → (q : x ≡ y) →
    x≢0 x {p} ≡ x≢0 y {ℝ\0≡-help p q}
  ℝ\0≡ _ refl = refl

  -x≢0 : {x : ℝ} → .(x ≢0) → - x ≢0
  -x≢0 {x} p -x≡0 = ⊥-irrelevant (p $ begin
    x       ≡˘⟨ +-identityʳ x ⟩
    x + 0ℝ  ≡˘⟨ cong (_+_ x) -x≡0 ⟩
    x + - x ≡⟨ -‿inverseʳ x ⟩
    0ℝ ∎)

  x⁻¹≢0 : {x : ℝ} → .(p : x ≢0) → (x≢0 x {p}) ⁻¹ ≢0
  x⁻¹≢0 {x} p x⁻¹≡0 = ⊥-irrelevant (p $ begin
    x                     ≡˘⟨ *-identityʳ x ⟩
    x · 1ℝ                ≡˘⟨ cong (_·_ x) (*-inverseʳ p) ⟩
    x · (x / (x≢0 x {p})) ≡⟨ cong (λ y → x · (x · y)) x⁻¹≡0 ⟩
    x · (x · 0ℝ)          ≡⟨ cong (_·_ x) (zeroʳ x) ⟩
    x · 0ℝ                ≡⟨ zeroʳ x ⟩
    0ℝ ∎)

  ⁻¹-distrib-* : {x y : ℝ} → .(p : x ≢0) → .(q : y ≢0) →
    (x≢0 (x · y) {x·y≢0 p q})⁻¹ ≡ (x≢0 x {p})⁻¹ · (x≢0 y {q})⁻¹
  ⁻¹-distrib-* {x} {y} p q = sym $ begin
      x⁻¹y⁻¹                      ≡˘⟨ *-identityʳ x⁻¹y⁻¹ ⟩
      x⁻¹y⁻¹ · unit               ≡˘⟨ cong (_·_ x⁻¹y⁻¹) (*-inverseʳ pq) ⟩
      x⁻¹y⁻¹ · ((x · y) · xy₀ ⁻¹) ≡˘⟨ *-assoc x⁻¹y⁻¹ (x · y) (xy₀ ⁻¹) ⟩
      (x⁻¹y⁻¹ · (x · y)) · xy₀ ⁻¹
        ≡⟨ cong (_· xy₀ ⁻¹) (*-comm-middle (x₀ ⁻¹) (y₀ ⁻¹) x y) ⟩
      (x₀ ⁻¹ · x) · (y₀ ⁻¹ · y) · xy₀ ⁻¹
        ≡⟨ cong₂ (λ a b → a · b · xy₀ ⁻¹) (*-inverseˡ p) (*-inverseˡ q) ⟩
      unit · unit · xy₀ ⁻¹        ≡⟨ cong (_· xy₀ ⁻¹) (*-identityˡ unit) ⟩
      unit · xy₀ ⁻¹               ≡⟨ *-identityˡ (xy₀ ⁻¹) ⟩
      xy₀ ⁻¹ ∎
      where
      x₀ = x≢0 x {p}
      y₀ = x≢0 y {q}
      xy₀ = x≢0 (x · y) {x·y≢0 p q}
      pq = x·y≢0 p q
      x⁻¹y⁻¹ = x₀ ⁻¹ · y₀ ⁻¹

  /-mul : (a b c d : ℝ) .{p : b ≢0} .{q : d ≢0} → let
    b₀ = x≢0 b {p}
    d₀ = x≢0 d {q}
    in a / b₀ · c / d₀ ≡ (a · c) / x≢0 (b · d) {x·y≢0 p q}
  /-mul a b c d {p} {q} = begin
      a / b₀ · c / d₀           ≡⟨ *-comm-middle a (b₀ ⁻¹) c (d₀ ⁻¹) ⟩
      (a · c) · (b₀ ⁻¹ · d₀ ⁻¹) ≡˘⟨ cong (_·_ (a · c))  (⁻¹-distrib-* p q) ⟩
      (a · c) / bd₀             ∎
      where
      b₀ = x≢0 b {p}
      d₀ = x≢0 d {q}
      bd₀ = x≢0 (b · d) {x·y≢0 p q}


  x/1 : (x : ℝ) → x / x≢0 unit {1≢0} ≡ x
  x/1 x rewrite sym (*-identityˡ ((x≢0 unit {1≢0})⁻¹)) | *-inverseʳ 1≢0 =
    *-identityʳ x

  /-simplˡ : (x y z : ℝ) .{p : x ≢0} .{q : z ≢0} →
    (x · y) / x≢0 (x · z) {x·y≢0 p q} ≡ y / x≢0 z {q}
  /-simplˡ x y z {p} {q} rewrite sym (/-mul x x y z {p} {q}) | *-inverseʳ p =
    *-identityˡ (y / x≢0 z {q})

  /-simplʳ : (x y z : ℝ) .{p : x ≢0} .{q : z ≢0} →
     (y · x) / x≢0 (z · x) {x·y≢0 q p} ≡ y / x≢0 z {q}
  /-simplʳ x y z {p} {q} = begin
    (y · x) / zx₀ ≡⟨ cong₂ _/_ (*-comm y x) (ℝ\0≡ (x·y≢0 q p) (*-comm z x)) ⟩
    (x · y) / xz₀ ≡⟨ /-simplˡ x y z {p} {q} ⟩
    y / z₀ ∎
    where
    zx₀ = x≢0 (z · x) {x·y≢0 q p}
    xz₀ = x≢0 (x · z) {x·y≢0 p q}
    z₀ = x≢0 z {q}


  /-coef : (x y z : ℝ) .{p : z ≢0} → x · y / x≢0 z {p} ≡ (x · y) / x≢0 z {p}
  /-coef x y z {p} rewrite sym (x/1 x) | /-mul x 1ℝ y z {1≢0} {p} | x/1 x
    | ⁻¹-distrib-* 1≢0 p | 1⁻¹ | *-identityˡ ((x≢0 z {p})⁻¹) = refl

  /-coef-simplˡ : (x y z : ℝ) .{p : x ≢0} .{q : z ≢0} →
    x · y / (x≢0 (x · z) {x·y≢0 p q}) ≡ y / (x≢0 z {q})
  /-coef-simplˡ x y z {p} {q} rewrite /-coef x y (x · z) {x·y≢0 p q} =
    /-simplˡ x y z {p} {q}

  private
    1/1/x-help : (x : ℝ) .{p : x ≢0} → x · 1ℝ / (x≢0 x {p}) ≡ 1ℝ
    1/1/x-help x {p} rewrite /-coef x 1ℝ x {p} | *-identityʳ x =
      *-inverseʳ p

  1/1/x : (x : ℝ) .{p : x ≢0} → let
    x₀ = x≢0 x {p}
    1/x = x≢0 (unit / x₀) {x·y≢0 1≢0 (x⁻¹≢0 p)}
    in unit / 1/x ≡ x
  1/1/x x {p} = begin
    1ℝ / 1/x           ≡˘⟨ cong (_· (1/x)⁻¹) (*-inverseʳ p) ⟩
    (x / x₀) / 1/x     ≡⟨ /-simplʳ (x₀ ⁻¹) x 1ℝ {x⁻¹≢0 p} {1≢0} ⟩
    x / 1ℝ\0 ≡⟨ x/1 x ⟩
    x ∎
    where
    x₀ = x≢0 x {p}
    1/x = x≢0 (unit / x₀) {x·y≢0 1≢0 (x⁻¹≢0 p)}

  ------------------
  -- Inequalities --
  ------------------

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

  --------------------
  -- Exponent rules --
  --------------------

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

