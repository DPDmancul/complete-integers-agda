
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe #-}

---------------
-- Utilities --
---------------

module Utils where
  open import Agda.Builtin.Equality

  transport : {A : Set} {x y : A} → (f : A → Set) → x ≡ y → f x → f y
  transport f refl s = s
