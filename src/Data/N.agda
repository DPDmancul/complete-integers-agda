
-- (c) Davide Peressoni 2022

---------------------
-- Integer numbers --
---------------------

module Data.N where
  open import Data.Nat hiding (_+_ ; _*_ ; _^_) public
  open import Data.Nat.Properties

  open import Ops

  instance
    Sumℕ : Sum ℕ
    _+_ ⦃ Sumℕ ⦄ = Data.Nat._+_

    additive-zero ⦃ Sumℕ ⦄ = 0
    lemma-sum-zero ⦃ Sumℕ ⦄ = +-identityˡ _

  instance
    Mulℕ : Mul ℕ
    _·_ ⦃ Mulℕ ⦄ = Data.Nat._*_

    unit ⦃ Mulℕ ⦄ = 1
    lemma-unit ⦃ Mulℕ ⦄ = *-identityˡ _


