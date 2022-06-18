
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
  open import Data.N hiding (_<_ ; _≤_ ; _>_ ; _≥_)
  open ℕ
  import Data.Nat.Properties as ℕp
  open import Data.Int hiding (∣_∣ ; suc ; _<_ ; _≤_ ; _>_ ; _≥_)
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

  ℝ∪0∣x∣₀≡∣ℝ∪0x∣ : (x : ℝ\0) → ℝ∪0 ∣ x ∣₀ ≡ ∣ ℝ∪0 x ∣
  ℝ∪0∣x∣₀≡∣ℝ∪0x∣ (x≢0 x) = refl

  ∣x∣∣y∣₀ : (x y : ℝ\0) → ∣ x ∣₀ · ∣ y ∣₀ ≡ ∣ x · y ∣₀
  ∣x∣∣y∣₀ (x≢0 x {p}) (x≢0 y {q}) = ℝ\0≡ (x·y≢0 (∣x∣≢0 p) (∣x∣≢0 q)) (∣x∣∣y∣ x y)

  -- --------------------
  -- -- Exponent rules --
  -- --------------------

  ℝ\0^0 : (x : ℝ\0) → x ^₀ 0 ≡ 1ℝ\0
  ℝ\0^0 (x≢0 _ {p}) = ℝ\0≡ (x^n≢0 p 0) refl

  ℝ\0^1 : (x : ℝ\0) → x ^₀ 1 ≡ x
  ℝ\0^1 (x≢0 x {p}) = ℝ\0≡ (x^n≢0 p 1) (*-identityʳ x)

  private
    sum-exp-help : {x : ℝ} .(p : x ≢0) → (n m : ℕ) → let
      x₀ = x≢0 x {p}
      in x₀ ^ (pos n  + -[1+ m ]) ≡ x₀ ^ pos n · x₀ ^ -[1+ m ]
    sum-exp-help {x} p 0       m = sym $ *-identityˡ
       ((x≢0 (x ^ suc m) {x^n≢0 p (suc m)})⁻¹)
    sum-exp-help {x} p (suc n) 0 rewrite /-simplˡ x (x ^ n) 1ℝ {p} {1≢0}
      | 1⁻¹ = sym $ *-identityʳ (x ^ n)
    sum-exp-help {x} p (suc n) (suc m) rewrite ℤp.[1+m]⊖[1+n]≡m⊖n n (suc m)
      | *-assoc (x ^ n) x (1ℝ / (x≢0 (x ^ suc (suc m)) {x^n≢0 p (suc (suc m))}))
      | /-simplˡ x (x ^ n) (x ^ suc m) {p} {x^n≢0 p (suc m)} =
        sum-exp-help p n m

  sum-exp : (x : ℝ\0) → (z w : ℤ) →  x ^ (z + w) ≡ x ^ z · x ^ w
  sum-exp (x≢0 x)     (pos n)  (pos m)  = sum-exp-ℕ x n m
  sum-exp (x≢0 _ {p}) (pos n)  -[1+ m ] = sum-exp-help p n m
  sum-exp (x≢0 x {p}) -[1+ n ] (pos m)
    rewrite *-comm ((x≢0 (x ^ suc n) {x^n≢0 p (suc n)})⁻¹) (x ^ m) =
    sum-exp-help p m n
  sum-exp (x≢0 x {p}) -[1+ n ] -[1+ m ] rewrite /-mul 1ℝ (x ^ suc n) 1ℝ
    (x · x ^ m) {x^n≢0 p (suc n)} {x^n≢0 p (suc m)}
    | *-identityˡ 1ℝ | *-assoc x (x ^ n) (x ^ suc m)
    | sym (*-assoc (x ^ n) x (x ^ m)) | *-comm (x ^ n) x
    | *-assoc x (x ^ n) (x ^ m)
    | sym $ ⁻¹-distrib-* (x^n≢0 p (suc n)) (x^n≢0 p (suc m)) =
    cong _⁻¹ $ ℝ\0≡ (x^n≢0 p (suc (suc (n + m)))) $ begin
    x ^ suc (suc (n + m)) ≡˘⟨ cong (λ n → x ^ suc n) (ℕp.+-suc n m) ⟩
    x ^ (suc n + suc m)   ≡⟨ sum-exp-ℕ x (suc n) (suc m) ⟩
    x ^ suc n · x ^ suc m ∎

  mul-base : (x y : ℝ\0) → (z : ℤ) → (x · y) ^ z ≡ x ^ z · y ^ z
  mul-base (x≢0 x)     (x≢0 y)     (pos n)  = mul-base-ℕ x y n
  mul-base (x≢0 x {p}) (x≢0 y {q}) -[1+ n ]
    rewrite sym $ ⁻¹-distrib-* (x^n≢0 p (suc n)) (x^n≢0 q (suc n)) =
    cong _⁻¹ $ ℝ\0≡ (x^n≢0 (x·y≢0 p q) (suc n)) (mul-base-ℕ x y (suc n))

  private
    double-exp-help : (x : ℝ\0) → (n m : ℕ) →
      ((x ^₀ n) ^₀ suc m)⁻¹ ≡ x ^ (pos n · -[1+ m ])
    double-exp-help x 0       m rewrite ℝ\0^0 x = trans
      (cong _⁻¹ $ ℝ\0≡ (x·y≢0 1≢0 (x^n≢0 1≢0 m)) $
        trans (*-identityˡ (1ℝ ^ m)) (1^n m)) 1⁻¹
    double-exp-help (x≢0 x {p}) (suc n) m = cong _⁻¹ $ ℝ\0≡
      (x·y≢0 (x^n≢0 p (suc n)) (x^n≢0 (x^n≢0 p (suc n)) m))
      (double-exp-ℕ x (suc n) (suc  m))

  -- mutual
  --   [1/x]^n : (x : ℝ\0) → (n : ℕ) → (x ⁻¹) ^ n ≡ (x ^₀ n)⁻¹
  --   [1/x]^n x₀@(x≢0 x {p}) n = begin
  --     (x₀ ⁻¹) ^ n               ≡⟨ {!   !} ⟩ --cong (λ x → (x ⁻¹) ^ n) (sym (*-identityʳ x)) ⟩
  --     (x₀ ⁻¹₀) ^ pos n          ≡⟨ {!   !} ⟩ --cong (λ x → (x ⁻¹) ^ n) (sym (*-identityʳ x)) ⟩
  --     (x₀ ^₀z -[1+ 0 ]) ^ pos n ≡⟨ {!   !} ⟩
  --     -- x ^ (-[1+ 0 ] · pos n) ≡⟨ cong (_^_ x) (ℤp.*-comm -[1+ 0 ] (pos n)) ⟩
  --     -- x ^ (pos n · -[1+ 0 ]) ≡˘⟨ (double-exp x {p} (pos n) -[1+ 0 ] ⟩
  --     -- (x ^ n) ^ -[1+ 0 ]     ≡⟨ cong (_/_ 1ℝ) (*-identityʳ (x ^ n)) ⟩
  --     (x₀ ^₀ n)⁻¹           ∎
  --     -- where
  --     -- helper : (x : ℝ\0) → (n : ℕ) → ((x · 1ℝ\0)⁻¹) ^ n ≡ x ^ (-[1+ 0 ] · pos n)
  --     -- helper x          0       rewrite ℝ\0^0 x = refl
  --     -- helper x₀@(x≢0 x) (suc n) rewrite helper x₀ n | ℕp.+-identityʳ n =
  --     --   {!   !}
  --       -- | *-identityʳ x = ? --with n
  --     -- ... | 0     rewrite *-identityʳ x | *-identityʳ (x ⁻¹) = refl
  --     -- ... | suc n rewrite /-mul 1ℝ x 1ℝ (x ^ suc n) | *-identityˡ 1ℝ = refl

  --   [x/y]^n : (x : ℝ) (y : ℝ\0) → (n : ℕ) → (x / y) ^ n ≡ (x ^ n) / (y ^₀ n)
  --   -- [x/y]^n x y {p} n rewrite sym (*-identityʳ x) | mul-base-ℕ x 1ℝ n | 1^n n
  --   --   | sym (/-coef (x ^ n) 1ℝ (y ^ n)) | sym ([1/x]^n y {p} n)
  --   --   | sym (mul-base-ℕ x (1ℝ / y) n) | /-coef x 1ℝ y = refl

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

