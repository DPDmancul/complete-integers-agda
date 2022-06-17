
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

  -- --------------------
  -- -- Exponent rules --
  -- --------------------

  ℝ\0^0 : (x : ℝ\0) → _^_ ⦃ NatPowℝ\0 ⦄ x 0 ≡ x≢0 1ℝ {1≢0}
  ℝ\0^0 (x≢0 _ {p}) = ℝ\0≡ (x^n≢0 p 0) refl

  ℝ\0^1 : (x : ℝ\0) → _^_ ⦃ NatPowℝ\0 ⦄ x 1 ≡ x
  ℝ\0^1 (x≢0 x {p}) = ℝ\0≡ (x^n≢0 p 1) (*-identityʳ x)

  private
    sum-exp-help : (x : ℝ\0) → (n m : ℕ) →
      x ^ (pos n  + -[1+ m ]) ≡ x ^ pos n · x ^ -[1+ m ]
    sum-exp-help (x≢0 x {p}) 0       m = sym $ *-identityˡ
       ((x≢0 (x ^ suc m) {x^n≢0 p (suc m)})⁻¹)
    sum-exp-help (x≢0 x {p}) (suc n) 0 rewrite /-simplˡ x (x ^ n) 1ℝ {p} {1≢0}
      | 1⁻¹ = sym $ *-identityʳ (x ^ n)
    sum-exp-help (x≢0 x {p}) (suc n) (suc m) rewrite ℤp.[1+m]⊖[1+n]≡m⊖n n (suc m)
      | *-assoc (x ^ n) x (1ℝ / (x≢0 (x ^ suc (suc m)) {x^n≢0 p (suc (suc m))}))
      | /-simplˡ x (x ^ n) (x ^ suc m) {p} {x^n≢0 p (suc m)} =
        sum-exp-help (x≢0 x {p}) n m

  sum-exp : (x : ℝ\0) → (z w : ℤ) → x ^ (z + w) ≡ x ^ z · x ^ w
  sum-exp (x≢0 x)        (pos n)  (pos m)  = sum-exp-ℕ x n m
  sum-exp x              (pos n)  -[1+ m ] = sum-exp-help x n m
  sum-exp x₀@(x≢0 x {p}) -[1+ n ] (pos m)
    rewrite *-comm ((x≢0 (x ^ suc n) {x^n≢0 p (suc n)})⁻¹) (x ^ m) =
    sum-exp-help x₀ m n
  sum-exp x₀@(x≢0 x {p}) -[1+ n ] -[1+ m ] rewrite /-mul 1ℝ (x ^ suc n) 1ℝ
    (x · x ^ m) {x^n≢0 p (suc n)} {x^n≢0 p (suc m)}
    | *-identityˡ 1ℝ | *-assoc x (x ^ n) (x ^ suc m)
    | sym (*-assoc (x ^ n) x (x ^ m)) | *-comm (x ^ n) x
    | *-assoc x (x ^ n) (x ^ m)
    | sym $ ⁻¹-distrib-* (x^n≢0 p (suc n)) (x^n≢0 p (suc m)) =
    cong _⁻¹ $ ℝ\0≡ (x^n≢0 p (suc (suc (n + m)))) $ begin
    x ^ suc (suc (n + m)) ≡˘⟨ cong (λ n → x ^ suc n) (ℕp.+-suc n m) ⟩
    x ^ (suc n + suc m)   ≡⟨ sum-exp-ℕ x (suc n) (suc m) ⟩
    x ^ suc n · x ^ suc m ∎

