
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
  -- open import Data.N hiding (_<_ ; _≤_ ; _>_ ; _≥_)
  -- open ℕ
  -- import Data.Nat.Properties as ℕp
  -- open import Data.Int hiding (∣_∣ ; suc ; _<_ ; _≤_ ; _>_ ; _≥_)
  -- open ℤ
  -- import Data.Int.Properties as ℤp
  open import Data.Empty
  open import Data.Sum
  -- open import Data.Product
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
    *-inverse : (x : ℝ\0) → (ℝ∪0 x) · x ⁻¹ ≡ unit

  x·y≡0 : (x y : ℝ) → x · y ≡ 0ℝ → x ≡ 0ℝ ⊎ y ≡ 0ℝ
  x·y≡0 x y p with isZero x
  ... | inj₁ x≡0 = inj₁ x≡0
  ... | inj₂ q   with isZero y
  ... | inj₁ y≡0 = inj₂ y≡0
  ... | inj₂ r   = helper $ r $ begin
    y                ≡˘⟨ *-identityˡ y ⟩
    1ℝ · y           ≡˘⟨ cong (_· y) (*-inverse x₀) ⟩
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

  x·y≢0 : {x y : ℝ} → x ≢0 → y ≢0 → x · y ≢0
  x·y≢0 {x} {y} p q xy≡0 with x·y≡0 x y xy≡0
  ... | inj₁ x≡0 = p x≡0
  ... | inj₂ y≡0 = q y≡0

  -x≢0 : {x : ℝ} → x ≢0 → - x ≢0
  -x≢0 {x} p -x≡0 = p $ begin
    x       ≡˘⟨ +-identityʳ x ⟩
    x + 0ℝ  ≡˘⟨ cong (_+_ x) -x≡0 ⟩
    x + - x ≡⟨ -‿inverseʳ x ⟩
    0ℝ ∎

  -- /-mul : (a b c d : ℝ) {p : b ≢0} {q : d ≢0} → let
  --   b₀ = x≢0 b {p}
  --   d₀ = x≢0 d {q}
  --   in a / b₀ · c / d₀ ≡ (a · c) / x≢0 (b · d) {x·y≢0 p q}
  -- /-mul a b c d = {!   !}

  -- x/1 : (x : ℝ) → x / x≢0 unit {1≢0} ≡ x
  -- x/1 x = {!   !}

  -- /-simplˡ : (x y z : ℝ) {p : x ≢0} {q : z ≢0} →
  --   (x · y) / x≢0 (x · z) {{!   !}} ≡ y / x≢0 z {q}
  -- /-simplˡ x y z {p} {q} rewrite sym (/-mul x x y z) | x/x x {p} =
  --   {!   !} --*-identityˡ (y / x≢0 z {q})

  -- /-coef : (x y z : ℝ) {p : z ≢0} → x · y / x≢0 z {p} ≡ (x · y) / x≢0 z {p}
  -- /-coef x y z = {!   !} --rewrite sym (x/1 x) | /-mul x 1ℝ y z | x/1 x | *-identityˡ z = refl

  -- /-coef-simplˡ : (x y z : ℝ) {_ : x ≢0} → x · y / (x · z) ≡ y / z
  -- /-coef-simplˡ x y z {p} rewrite /-coef x y (x · z) = /-simplˡ x y z {p}

  -- private
  --   1/1/x-help : (x : ℝ) {_ : x ≢0} → x · 1ℝ / x ≡ 1ℝ
  --   1/1/x-help x {p} rewrite /-coef x 1ℝ x | *-identityʳ x =  x/x x {p}

  -- 1/1/x : (x : ℝ) {_ : x ≢0} → unit / (unit / x) ≡ x
  -- 1/1/x x {p} rewrite sym (*-identityˡ (1ℝ / (1ℝ / x)))
  --   | sym (x/x x {p}) | /-mul x x (x / x) ((x / x) / x) | x/x x {p}
  --   | 1/1/x-help x {p} | sym (/-coef x 1ℝ 1ℝ) | x/1 1ℝ = *-identityʳ x

  -- ∣x∣∣x∣ : (x : ℝ) → ∣ x ∣ · ∣ x ∣ ≡ x ^ 2
  -- ∣x∣∣x∣ x rewrite *-identityʳ x with ≤-total x 0ℝ
  -- ... | inj₁ x≤0 = refl
  -- ... | inj₂ x≥0 = *-cancel-neg x x

  -- ∣x∣∣y∣ : (x y : ℝ) → ∣ x ∣ · ∣ y ∣ ≡ ∣ x · y ∣
  -- ∣x∣∣y∣ x y = ?

  -- --------------------
  -- -- Exponent rules --
  -- --------------------

  -- import Data.Integer.Properties as ℤp

  -- sum-exp-ℕ : (x : ℝ) → (n m : ℕ) → x ^ (n + m) ≡ x ^ n · x ^ m
  -- sum-exp-ℕ x zero      m = sym (*-identityˡ (x ^ m))
  -- sum-exp-ℕ x (ℕ.suc n) m rewrite *-assoc x (x ^ n) (x ^ m) =
  --   cong (_·_ x) (sum-exp-ℕ x n m)

  -- private
  --   sum-exp-help : (x : ℝ) {_ : x ≢0} → (n m : ℕ) →
  --     x ^ (pos n  + -[1+ m ]) ≡ x ^ pos n · x ^ -[1+ m ]
  --   sum-exp-help x     0       m = sym (*-identityˡ  (1ℝ / (x · x ^ m)))
  --   sum-exp-help x {p} (suc n) 0 rewrite *-comm x (x ^ n)
  --     | *-assoc (x ^ n) x (1ℝ / (x · 1ℝ)) | /-coef-simplˡ x 1ℝ 1ℝ {p}
  --     | x/x 1ℝ {1≢0} = sym (*-identityʳ (x ^ n))
  --   sum-exp-help x {p} (suc n) (suc m) rewrite ℤp.[1+m]⊖[1+n]≡m⊖n n (suc m)
  --     | *-comm x (x ^ n) | *-assoc (x ^ n) x (1ℝ / (x · (x · x ^ m)))
  --     | /-coef-simplˡ x 1ℝ (x · x ^ m) {p} = sum-exp-help x {p} n m

  -- sum-exp : (x : ℝ) {_ : x ≢0} → (z w : ℤ) → x ^ (z + w) ≡ x ^ z · x ^ w
  -- sum-exp x     (pos n)  (pos m)  = sum-exp-ℕ x n m
  -- sum-exp x {p} (pos n)  -[1+ m ] = sum-exp-help x {p} n m
  -- sum-exp x {p} -[1+ n ] (pos m)  rewrite *-comm (1ℝ / (x · x ^ n)) (x ^ m) =
  --   sum-exp-help x {p} m n
  -- sum-exp x {p} -[1+ n ] -[1+ m ] rewrite /-mul 1ℝ (x · x ^ n) 1ℝ (x · x ^ m)
  --   | *-identityˡ 1ℝ | *-assoc x (x ^ n) (x · x ^ m)
  --   | sym (*-assoc (x ^ n) x (x ^ m)) | *-comm (x ^ n) x
  --   | *-assoc x (x ^ n) (x ^ m) =
  --   cong (λ y →  1ℝ / (x · (x · y))) (sum-exp-ℕ x n m)

  -- mul-base-ℕ : (x y : ℝ) → (n : ℕ) → (x · y) ^ n ≡ x ^ n · y ^ n
  -- mul-base-ℕ x y 0       = sym (*-identityʳ 1ℝ)
  -- mul-base-ℕ x y (suc n) rewrite *-comm-middle x (x ^ n) y (y ^ n) =
  --   cong (_·_ (x · y)) (mul-base-ℕ x y n)

  -- mul-base : (x y : ℝ) → (z : ℤ) → (x · y) ^ z ≡ x ^ z · y ^ z
  -- mul-base x y (pos n)  = mul-base-ℕ x y n
  -- mul-base x y -[1+ n ] rewrite /-mul 1ℝ (x ^ suc n) 1ℝ (y ^ suc n)
  --   | *-identityˡ 1ℝ = cong (_/_ 1ℝ) (mul-base-ℕ x y (suc n))

  -- 1^n : (n : ℕ) → 1ℝ ^ n ≡ 1ℝ
  -- 1^n 0       = refl
  -- 1^n (suc n) rewrite 1^n n = *-identityˡ 1ℝ

  -- double-exp-ℕ : (x : ℝ) → (n m : ℕ) → (x ^ n) ^ m ≡ x ^ (n · m)
  -- double-exp-ℕ x 0       m = 1^n m
  -- double-exp-ℕ x (suc n) m rewrite mul-base-ℕ x (x ^ n) m
  --   | double-exp-ℕ x n m = sym (sum-exp-ℕ x m (n · m))

  -- x^nm=x^mn : (x : ℝ) → (n m : ℕ) → (x ^ n) ^ m ≡ (x ^ m) ^ n
  -- x^nm=x^mn x n m rewrite double-exp-ℕ x n m | ℕp.*-comm n m =
  --   sym (double-exp-ℕ x m n)

  -- private
  --   double-exp-help : (x : ℝ) → (n m : ℕ) →
  --     1ℝ / ((x ^ n) ^ suc m) ≡ x ^ (pos n · -[1+ m ])
  --   double-exp-help x 0       m rewrite 1^n m | *-identityˡ 1ℝ = x/1 1ℝ
  --   double-exp-help x (suc n) m = cong (_/_ 1ℝ) (double-exp-ℕ x (suc n) (suc  m))

  -- mutual
  --   [1/x]^n : (x : ℝ) {_ : x ≢0} → (n : ℕ) → (1ℝ / x) ^ n ≡ 1ℝ / (x ^ n)
  --   [1/x]^n x {p} n = begin
  --     (1ℝ / x) ^ pos n ≡⟨ cong (λ x → (1ℝ / x) ^ n) (sym (*-identityʳ x)) ⟩
  --     (x ^ -[1+ 0 ]) ^ pos n ≡⟨ helper x n ⟩
  --     x ^ (-[1+ 0 ] · pos n) ≡⟨ cong (_^_ x) (ℤp.*-comm -[1+ 0 ] (pos n)) ⟩
  --     x ^ (pos n · -[1+ 0 ]) ≡˘⟨ (double-exp x {p} (pos n) -[1+ 0 ] ⟩
  --     (x ^ n) ^ -[1+ 0 ]     ≡⟨ cong (_/_ 1ℝ) (*-identityʳ (x ^ n)) ⟩
  --     1ℝ / (x ^ n)           ∎
  --     where
  --     helper : (x : ℝ) → (n : ℕ) → (1ℝ / (x · 1ℝ)) ^ n ≡ x ^ (-[1+ 0 ] · pos n)
  --     helper x 0             = refl
  --     helper x (suc n) rewrite helper x n | ℕp.+-identityʳ n | *-identityʳ x
  --       with n
  --     ... | 0     rewrite *-identityʳ x | *-identityʳ (1ℝ / x) = refl
  --     ... | suc n rewrite /-mul 1ℝ x 1ℝ (x ^ suc n) | *-identityˡ 1ℝ = refl

  --   [x/y]^n : (x y : ℝ) {_ : y ≢0} → (n : ℕ) → (x / y) ^ n ≡ (x ^ n) / (y ^ n)
  --   [x/y]^n x y {p} n rewrite sym (*-identityʳ x) | mul-base-ℕ x 1ℝ n | 1^n n
  --     | sym (/-coef (x ^ n) 1ℝ (y ^ n)) | sym ([1/x]^n y {p} n)
  --     | sym (mul-base-ℕ x (1ℝ / y) n) | /-coef x 1ℝ y = refl

  --   double-exp : (x : ℝ) {_ : x ≢0} → (z w : ℤ) → (x ^ z) ^ w ≡ x ^ (z · w)
  --   double-exp x     (pos n)  (pos m)  rewrite ℤp.pos-mul n m =
  --     double-exp-ℕ x n m
  --   double-exp x     (pos n)  -[1+ m ] = double-exp-help x n m
  --   double-exp x {p} -[1+ n ] (pos m)
  --     rewrite [1/x]^n (x ^ suc n) {x^n≢0 x {p} (suc n)} m
  --     | x^nm=x^mn x (suc n) m | ℤp.*-comm -[1+ n ] (pos m) =
  --     double-exp-help x m n
  --   double-exp x {p} -[1+ n ] -[1+ m ]
  --     rewrite [1/x]^n (x ^ suc n) {x^n≢0 x {p} (suc n)} m
  --     | /-mul 1ℝ (x ^ suc n) 1ℝ ((x ^ suc n) ^ m) | *-identityˡ 1ℝ
  --     | double-exp-ℕ x (suc n) m | sym (sum-exp-ℕ x (suc n) (m + n · m))
  --     | 1/1/x (x ^ suc (n + (m + (n · m))))
  --     {x^n≢0 x {p} (suc (n + (m + (n · m))))} =
  --     cong (λ y → x ^ suc y) (helper n m)
  --     where
  --     helper : (n m : ℕ) → n + (m + n · m) ≡ m + (n · suc m)
  --     helper n m rewrite ℕp.*-comm n (suc m) | ℕp.*-comm m n = begin
  --       (n + (m + n · m)) ≡˘⟨ ℕp.+-assoc n m (n · m) ⟩
  --       ((n + m) + n · m) ≡⟨ cong (_+ n · m) (ℕp.+-comm n m) ⟩
  --       ((m + n) + n · m) ≡⟨ ℕp.+-assoc m n (n · m) ⟩
  --       (m + (n + n · m)) ∎
