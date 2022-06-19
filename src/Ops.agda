
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
  record Operator-^ (S : Set) : Set where

    infixr 8 _^_
    field _^_ : S

  open Operator-^ ⦃ ... ⦄ public

  Pow : (B E : Set) {R : Set} → Set
  Pow B E {R} = Operator-^ (B → E → R)
  CertPow : (B E : Set) {C : B → Set} {R : Set} → Set
  CertPow B E {C} {R} = Operator-^ ((b : B) → E → .⦃ C b ⦄ → R)

  -- Power with natural exponents
  instance
    open import Agda.Builtin.Nat
    NatPow : {A : Set} ⦃ _ : Mul A ⦄ → Pow A Nat {A}
    _^_ ⦃ NatPow ⦄ = helper
      where
      helper : {A : Set} ⦃ _ : Mul A ⦄ → A → Nat → A
      helper _ zero    = unit
      helper b (suc e) = b · helper b e


