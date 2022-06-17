
-- (c) Davide Peressoni 2022

{-# OPTIONS --without-K #-}

-----------------------------
-- Postulated real numbers --
-----------------------------

module Data.PostulatedReals.Core where

  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import Data.Empty
  open import Data.Sum
  open import Data.Product
  open import Function.Base

  postulate
    ℝ : Set
    0ℝ : ℝ
    1ℝ : ℝ

  infix 4 _≢0
  _≢0 : ℝ → Set
  x ≢0 = x ≡ 0ℝ → ⊥

  data ℝ\0 : Set where
    x≢0 : (x : ℝ) → .{_ : x ≢0} → ℝ\0

  ℝ∪0 : ℝ\0 → ℝ
  ℝ∪0 (x≢0 x) = x

  infix 8 _⁻¹
  infix 4 _≤_ _≥_ _<_ _>_

  postulate
    addℝ : ℝ → ℝ → ℝ
    negℝ : ℝ → ℝ
    mulℝ : ℝ → ℝ → ℝ
    _⁻¹₀ : (x : ℝ\0) → ℝ\0

    _≤_ : ℝ → ℝ → Set

    1≢0 : 1ℝ ≢0
    isZero : (x : ℝ) → x ≡ 0ℝ ⊎ x ≢0

  data _<_ : ℝ → ℝ → Set where
    *<* : (x y : ℝ) → x ≤ y × (x ≡ y → ⊥) → x < y

  _>_ : ℝ → ℝ → Set
  x > y = y < x

  _≥_ : ℝ → ℝ → Set
  x ≥ y = y ≤ x

  open import Ops

  postulate
    lemma-+-identityˡ : (x : ℝ) → addℝ 0ℝ x ≡ x
    lemma-*-identityˡ : (x : ℝ) → mulℝ 1ℝ x ≡ x

  instance
    Sumℝ : Sum ℝ
    _+_ ⦃ Sumℝ ⦄ = addℝ
    additive-zero ⦃ Sumℝ ⦄ = 0ℝ
    lemma-sum-zero ⦃ Sumℝ ⦄ {x} = lemma-+-identityˡ x

    Subℝ : Sub ℝ
    -_ ⦃ Subℝ ⦄ = negℝ

    Mulℝ : Mul ℝ
    _·_ ⦃ Mulℝ ⦄ = mulℝ
    unit ⦃ Mulℝ ⦄ = 1ℝ
    lemma-unit ⦃ Mulℝ ⦄ {x} = lemma-*-identityˡ x

  _⁻¹ : (x : ℝ\0) → ℝ
  x ⁻¹ = ℝ∪0 (x ⁻¹₀)

  _/_ : (x : ℝ) → (y : ℝ\0) → ℝ
  x / y = x · y ⁻¹

  -1ℝ : ℝ
  -1ℝ = - unit

