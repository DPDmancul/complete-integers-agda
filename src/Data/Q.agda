
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

---------------------
-- Integer numbers --
---------------------

module Data.Q where
  open import Data.Rational hiding (_+_ ; -_ ; _-_ ; _*_) public
  open import Data.Rational.Properties

  open import Ops

  instance
    Sumℚ : Sum ℚ
    _+_ ⦃ Sumℚ ⦄ = Data.Rational._+_

    additive-zero ⦃ Sumℚ ⦄ = 0ℚ
    lemma-sum-zero ⦃ Sumℚ ⦄ = +-identityˡ _

  instance
    Subℚ : Sub ℚ
    -_ ⦃ Subℚ ⦄ = Data.Rational.-_

  instance
    Mulℚ : Mul ℚ
    _·_ ⦃ Mulℚ ⦄ = Data.Rational._*_

    unit ⦃ Mulℚ ⦄ = 1ℚ
    lemma-unit ⦃ Mulℚ ⦄ = *-identityˡ _

  open import Relation.Binary
  open import Data.Sum
  open import Agda.Builtin.Bool
  open import Relation.Nullary

  ≤-<-connex : Connex _≤_ _<_
  ≤-<-connex p q with p ≤? q
  ... | yes p≤q = inj₁ p≤q
  ... | no ¬p≤q = inj₂ (≰⇒> ¬p≤q)

