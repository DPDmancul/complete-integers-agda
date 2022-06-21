
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

----------------------------------
-- Properties of field modulo 2 --
----------------------------------

module Data.Int.Properties where
  open import Data.Integer.Properties public

  open import Relation.Binary.PropositionalEquality
  open import Data.Int
  open ℤ
  open import Data.N
  import Data.Nat.Properties as ℕp
  open import Utils
  open import Ops

  +-assoc-middle : (a b c d : ℤ) → (a + b) + (c + d) ≡ a + (b + c) + d
  +-assoc-middle = •-assoc-middle _+_ +-assoc

  +-comm-middle : (a b c d : ℤ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +-comm-middle = •-comm-middle _+_ +-comm +-assoc-middle

  +-inverse-middleˡ : (a b c : ℤ) → (a - b) + (b + c) ≡ a + c
  +-inverse-middleˡ = •-inverse-middleˡ _+_ -_ 0ℤ +-assoc +-inverseˡ +-identityʳ

  pos-mul : (n m : ℕ) → pos n · pos m ≡ pos (n · m)
  pos-mul n m with n · m
  ... | 0     = refl
  ... | suc _ = refl

