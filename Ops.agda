
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

    infixl 7 _*_
    field _*_ : A → A → A

    field
      unit : A
      lemma-unit : {a : A} → unit * a ≡ a

  open Mul ⦃ ... ⦄ public

  ----------------------------
  -- General Multiplication --
  ----------------------------
  record Multiplication (A B : Set) {C : Set} : Set where

    infixl 7 _·_
    field _·_ : A → B → C

  open Multiplication ⦃ ... ⦄ public

  instance
    MulMultiplication : {A : Set} ⦃ _ : Mul A ⦄ → Multiplication A A {A}
    _·_ ⦃ MulMultiplication ⦄ = _*_

  --------------------------------
  -- Times (Sum exponentiation) --
  --------------------------------
  instance
    open import Agda.Builtin.Nat hiding (_+_)
    open import Data.Integer hiding (_+_ ; -_)

    private
      open import Data.Empty

      data NatOrInt : Set → Set where
        nat : NatOrInt Nat
        int : NatOrInt ℤ

  -- Times with natural coefficients
    NatTimesˡ : {A : Set} {_ : NatOrInt A → ⊥} ⦃ _ : Sum A ⦄ → Multiplication Nat A {A}
    _·_ ⦃ NatTimesˡ ⦄ zero    _ = additive-zero
    _·_ ⦃ NatTimesˡ ⦄ (suc e) b = b + e · b

    NatTimesʳ : {A : Set} ⦃ _ : Sum A ⦄ → Multiplication A Nat {A}
    _·_ ⦃ NatTimesʳ ⦄ a b = b · a

  -- Times with integer coefficients
    IntTimesˡ : {A : Set} ⦃ _ : Sum A ⦄ ⦃ _ : Sub A ⦄ → Multiplication ℤ A {A}
    _·_ ⦃ IntTimesˡ ⦄ (ℤ.pos e)  b = e · b
    _·_ ⦃ IntTimesˡ ⦄ (-[1+_] e) b = - (Nat.suc e · b)

    IntTimesʳ : {A : Set} ⦃ _ : Sum A ⦄ ⦃ _ : Sub A ⦄ → Multiplication A ℤ {A}
    _·_ ⦃ IntTimesʳ ⦄ a b = b · a

  ------------------------------
  -- Pow (Mul exponentiation) --
  ------------------------------
  record Pow (B E : Set) {R : Set} : Set where

    infixl 8 _^_
    field _^_ : B → E → R

  open Pow ⦃ ... ⦄ public

  -- Power with natural exponents
  instance
    open import Agda.Builtin.Nat
    NatPow : {A : Set} ⦃ _ : Mul A ⦄ → Pow A Nat {A}
    _^_ ⦃ NatPow ⦄ _ zero    = unit
    _^_ ⦃ NatPow ⦄ b (suc e) = b · b ^ e


