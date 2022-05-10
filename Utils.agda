
-- (c) Davide Peressoni 2022

---------------
-- Utilities --
---------------

module Utils where

  --------------
  -- Equality --
  --------------
  module Equality {A : Set} {x y : A } where

    open import Agda.Builtin.Equality public

    -- Congruence
    cong : {B : Set} → (f : A → B) → x ≡ y → f x ≡ f y
    cong _ refl = refl

    -- Symmetry
    sym : x ≡ y → y ≡ x
    sym refl = refl

    -- Transitivity
    trans : {z : A} → x ≡ y → y ≡ z → x ≡ z
    trans refl p = p

  open Equality public


  --------------
  -- Naturals --
  --------------

  module Nat where

    open import Agda.Builtin.Nat renaming (_+_ to _+ℕ_; _-_ to _-ℕ_)

    lemma-plus-zero : (a : Nat) → a +ℕ 0 ≡ a
    lemma-plus-zero zero = refl
    lemma-plus-zero (suc a) = cong suc (lemma-plus-zero a)

  open Nat public


