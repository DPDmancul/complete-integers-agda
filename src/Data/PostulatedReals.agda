
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
  open import Data.N hiding (_<_ ; _≤_ ; _>_ ; _≥_ ; NonZero ; ≢-nonZero)
  open ℕ
  open import Data.Int hiding (∣_∣ ; suc ; _<_ ; _≤_ ; _>_ ; _≥_ ; NonZero ; ≢-nonZero)
  open ℤ
  open import Data.Sum
  open import Utils
  open import Function.Base
  open import Ops

  open import Data.PostulatedReals.Core public
  open import Data.PostulatedReals.CoreProperties

  ∣_∣ : ℝ → ℝ
  ∣ x ∣ with ≤-total x 0ℝ
  ... | inj₁ x≤0 = - x
  ... | inj₂ x≥0 = x

  ∣x∣≢0 : {x : ℝ} → x ≢0 → ∣ x ∣ ≢0
  ∣x∣≢0 {x} p  with ≤-total x 0ℝ
  ... | inj₁ x≤0 = -x≢0 p
  ... | inj₂ x≥0 = p

  instance
    ∣x∣-nonZero : {x : ℝ} .⦃ _ : NonZero x ⦄ → NonZero (∣ x ∣)
    ∣x∣-nonZero ⦃ p ⦄ = ≢-nonZero $ ∣x∣≢0 (≢-nonZero⁻¹ p)

  sgn : (x : ℝ) .⦃ _ : NonZero x ⦄ → ℝ
  sgn x with ≤-total x 0ℝ
  ... | inj₁ x≤0 = -1ℝ
  ... | inj₂ x≥0 = 1ℝ

  x^n≢0 : {x : ℝ} → x ≢0 → (n : ℕ) → x ^ n ≢0
  x^n≢0     _ 0       q = 1≢0 q
  x^n≢0 {x} p (suc n) q  with x·y≡0 x (x ^ n) q
  ... | inj₁ x≡0   = p x≡0
  ... | inj₂ x^n≡0 with x^n≢0 p n
  ... | s = s x^n≡0

  instance
    x^n-nonZero : {x : ℝ} .⦃ _ : NonZero x ⦄ → {n : ℕ} → NonZero (x ^ n)
    x^n-nonZero ⦃ p ⦄ {n} = ≢-nonZero $ x^n≢0 (≢-nonZero⁻¹ p) n

    IntPowℝ : Pow ℝ ℤ {NonZero} {ℝ}
    _^_ ⦃ IntPowℝ ⦄ b (pos n)        = b ^ n
    _^_ ⦃ IntPowℝ ⦄ b -[1+ n ] ⦃ p ⦄ = ((b ^ (suc n)) ⁻¹)
      ⦃ x^n-nonZero ⦃ p ⦄ {suc n} ⦄


