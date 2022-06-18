
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

---------------
-- Operators --
---------------

module Ops where

  open import Agda.Builtin.Equality
  open import Function.Base

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

  --------------------------------
  -- Times (Sum exponentiation) --
  --------------------------------
  record Times (A B : Set) {C : Set} : Set where

    infixl 7 _×_
    field _×_ : A → B → C

  open Times ⦃ ... ⦄ public

  instance
    open import Agda.Builtin.Nat hiding (_+_)
    open import Data.Integer hiding (_+_ ; -_)

  -- Times with natural coefficients
    NatTimesˡ : {A : Set} ⦃ _ : Sum A ⦄ → Times Nat A {A}
    _×_ ⦃ NatTimesˡ ⦄ = helper
      where
      helper : {A : Set} ⦃ _ : Sum A ⦄ → Nat → A → A
      helper zero    _ = additive-zero
      helper (suc e) b = b + helper e b

    NatTimesʳ : {A : Set} ⦃ _ : Sum A ⦄ → Times A Nat {A}
    _×_ ⦃ NatTimesʳ ⦄ a b = b × a

  -- Times with integer coefficients
    IntTimesˡ : {A : Set} ⦃ _ : Sum A ⦄ ⦃ _ : Sub A ⦄ → Times ℤ A {A}
    _×_ ⦃ IntTimesˡ ⦄ (ℤ.pos e)  b = e × b
    _×_ ⦃ IntTimesˡ ⦄ (-[1+_] e) b = - (Nat.suc e × b)

    IntTimesʳ : {A : Set} ⦃ _ : Sum A ⦄ ⦃ _ : Sub A ⦄ → Times A ℤ {A}
    _×_ ⦃ IntTimesʳ ⦄ a b = b × a

  ------------------------------
  -- Pow (Mul exponentiation) --
  ------------------------------
  record Pow (B E : Set) {C : B → Set} {R : Set} : Set where
    -- C could be used to certificate the base be different of zero
    -- if not required insert a type with an instance for all values of base

    infixr 8 _^_
    field _^_ : (b : B) → E → .⦃ C b ⦄ → R

  open Pow ⦃ ... ⦄ public

  -- Power with natural exponents
  instance
    open import Agda.Builtin.Nat
    -- Sum A is a naïve certificate, implied by Mul A
    NatPow : {A : Set} ⦃ _ : Mul A ⦄ → Pow A Nat {const $ Sum A} {A}
    _^_ ⦃ NatPow ⦄ = helper
      where
      helper : {A : Set} ⦃ _ : Mul A ⦄ → A → Nat → .⦃ _ : Sum A ⦄ → A
      helper _ zero    = unit
      helper b (suc e) = b · helper b e


