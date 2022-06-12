
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

------------------------
-- Continuation monad --
------------------------

module Monad (⊥ : Set) where

  infixr 3 ¬_
  ¬_ : Set → Set
  ¬ X = X → ⊥

  infixr 0 Prom_
  Prom_ : Set → Set
  Prom X = ¬ ¬ X

  return : {X : Set} → X → Prom X
  return x k = k x

  _⟫=_ : {A B : Set} → Prom A → (A → Prom B) → Prom B
  k ⟫= f = λ x → k (λ y → f y x)

  ⊥-elim : {X : Set} → ⊥ → Prom X
  ⊥-elim r k = r

  escape : Prom ⊥ → ⊥
  escape f = f (λ x → x)

