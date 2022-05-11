
-- (c) Davide Peressoni 2022

--------------
-- Equality --
--------------

module Utils.Equality {A : Set} {x y : A } where

  open import Agda.Builtin.Equality public

  -- Congruence
  cong : {B : Set} (f : A → B) → x ≡ y → f x ≡ f y
  cong _ refl = refl

  cong2 : {B C : Set} {w z : B} (f : A → B → C) → x ≡ y → w ≡ z → f x w ≡ f y z
  cong2 _ refl refl = refl

  -- Symmetry
  sym : x ≡ y → y ≡ x
  sym refl = refl

  -- Transitivity
  trans : {z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl p = p

