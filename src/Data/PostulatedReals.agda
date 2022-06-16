
-- (c) Davide Peressoni 2022

{-# OPTIONS --without-K #-}

-----------------------------
-- Postulated real numbers --
-----------------------------

-- I tried defining real numbers (R.agda) but it was taking too much time and
-- also loading the file and giving goals a value was consuming too much RAM.
-- So here I postulate the real numbers and their properties I need in my work.

module Data.PostulatedReals where

  open import Relation.Binary.PropositionalEquality
  open import Data.N hiding (_<_ ; _≤_ ; _>_ ; _≥_)
  open ℕ
  open import Data.Int hiding (∣_∣ ; suc ; _<_ ; _≤_ ; _>_ ; _≥_)
  open ℤ
  open import Data.Sum
  open import Ops

  open import Data.PostulatedReals.Core public
  open import Data.PostulatedReals.CoreProperties

  ∣_∣ : ℝ → ℝ
  ∣ x ∣ with ≤-total x 0ℝ
  ... | inj₁ x≤0 = x
  ... | inj₂ x≥0 = - x

  ∣_∣₀ : ℝ\0 → ℝ\0
  ∣ (x₀@(x≢0 x {p})) ∣₀ with ≤-total x 0ℝ
  ... | inj₁ x≤0 = x₀
  ... | inj₂ x≥0 = x≢0 (- x) { -x≢0 p}

  sgn : ℝ\0 → ℝ\0
  sgn (x≢0 x) with ≤-total x 0ℝ
  ... | inj₁ x≤0 = x≢0 -1ℝ { -x≢0 1≢0}
  ... | inj₂ x≥0 = x≢0 1ℝ {1≢0}

  x^n≢0 : {x : ℝ} → x ≢0 → (n : ℕ) → x ^ n ≢0
  x^n≢0     _ 0       q = 1≢0 q
  x^n≢0 {x} p (suc n) q  with x·y≡0 x (x ^ n) q
  ... | inj₁ x≡0   = p x≡0
  ... | inj₂ x^n≡0 with x^n≢0 p n
  ... | s = s x^n≡0

  instance
    NatPowℝ\0 : Pow ℝ\0 ℕ {ℝ\0}
    _^_ ⦃ NatPowℝ\0 ⦄ (x≢0 b {p}) n = x≢0 (b ^ n) {x^n≢0 p n}

    IntPowℝ\0 : Pow ℝ\0 ℤ {ℝ}
    _^_ ⦃ IntPowℝ\0 ⦄ b (pos n) = ℝ∪0 (_^_ ⦃ NatPowℝ\0 ⦄ b n)
    _^_ ⦃ IntPowℝ\0 ⦄ b -[1+ n ]  = (_^_ ⦃ NatPowℝ\0 ⦄ b (suc n)) ⁻¹

