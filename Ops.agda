
-- (c) Davide Peressoni 2022

---------------
-- Operators --
---------------

module Ops where

  open import Agda.Builtin.Equality

  ---------
  -- Sum --
  ---------
  record Sum (A : Set) : Set where

    infixl 8 +_
    +_ : A → A
    + x = x

    infixl 6 _+_
    field _+_ : A → A → A

    field
      additive-zero : A
      lemma-sum-zero : {a : A} → additive-zero + a ≡ a

  open Sum ⦃ ... ⦄ public

  ---------
  -- Sub --
  ---------
  record Sub (A : Set) ⦃ _ : Sum A ⦄ : Set where

    infixl 8 -_
    field -_ : A → A

    infixl 6 _-_
    _-_ : A → A → A
    a - b = a + (- b)

  open Sub ⦃ ... ⦄ public

  ---------
  -- Mul --
  ---------
  record Mul (A : Set) : Set where

    infixl 7 _·_
    field _·_ : A → A → A

    field
      unit : A
      lemma-unit : {a : A} → unit · a ≡ a

  open Mul ⦃ ... ⦄ public

  ---------
  -- Pow --
  ---------
  record Pow (B E : Set) {R : Set} : Set where

    infixl 8 _^_
    field _^_ : B → E → R

  open Pow ⦃ ... ⦄ public

  -- Power with natural exponents
  instance
    open import Agda.Builtin.Nat
    NatPow : {A : Set} ⦃ _ : Mul A ⦄ → Pow A Nat {A}
    _^_ ⦃ NatPow ⦄ _ zero = unit
    _^_ ⦃ NatPow ⦄ b (suc e) = b · b ^ e



