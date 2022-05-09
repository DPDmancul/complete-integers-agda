
-- (c) Davide Peressoni 2022

---------------
-- Operators --
---------------

module Ops where

  ---------
  -- Sum --
  ---------
  record Sum (A : Set) : Set where

    infixl 8 +_
    +_ : A → A
    + x = x

    infixl 6 _+_
    field _+_ : A → A → A

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

    infixl 6 _·_
    field _·_ : A → A → A

  open Mul ⦃ ... ⦄ public


