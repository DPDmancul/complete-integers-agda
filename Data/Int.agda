
-- (c) Davide Peressoni 2022

---------------------
-- Integer numbers --
---------------------

module Data.Int where
  open import Data.Integer hiding (_+_ ; -_ ; _-_ ; _*_) public
  open import Data.Integer.Properties

  open import Ops

  instance
    Sumℤ : Sum ℤ
    _+_ ⦃ Sumℤ ⦄ = Data.Integer._+_

    additive-zero ⦃ Sumℤ ⦄ = 0ℤ
    lemma-sum-zero ⦃ Sumℤ ⦄ {a} = +-identityˡ a

  instance
    Negateℤ : Sub ℤ
    -_ ⦃ Negateℤ ⦄ = Data.Integer.-_

  instance
    Mulℤ : Mul ℤ
    _·_ ⦃ Mulℤ ⦄ = Data.Integer._*_

    unit ⦃ Mulℤ ⦄ = 1ℤ
    lemma-unit ⦃ Mulℤ ⦄ {a} = *-identityˡ a


