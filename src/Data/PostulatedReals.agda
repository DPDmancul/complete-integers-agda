
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
  open import Data.N
  open import Data.Int hiding (∣_∣)

  postulate
    ℝ : Set
    0ℝ : ℝ
    1ℝ : ℝ

    addℝ : ℝ → ℝ → ℝ
    negℝ : ℝ → ℝ
    mulℝ : ℝ → ℝ → ℝ
    _/_ : ℝ → ℝ → ℝ
    ∣_∣ : ℝ → ℝ

  open import Ops

  private postulate
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

    IntPowℝ : Pow ℝ ℤ {ℝ}
    _^_ ⦃ IntPowℝ ⦄ b (ℤ.pos n) = b ^ n
    _^_ ⦃ IntPowℝ ⦄ b -[1+ n ]  = unit / (b ^ ℕ.suc n)


  ----------------
  -- Properties --
  ----------------

  module Properties where

    +-identityˡ = lemma-+-identityˡ
    *-identityˡ = lemma-*-identityˡ


