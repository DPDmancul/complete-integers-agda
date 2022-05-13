
-- (c) Davide Peressoni 2022

module Data.F2.Properties where
  open import Data.Bool.Properties public

  open import Relation.Binary.PropositionalEquality
  open import Data.F2
  open import Data.N
  open import Ops

  ⊕-assoc : (a b c : 𝔽₂) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
  ⊕-assoc zero _    _ = refl
  ⊕-assoc one  zero _ = refl
  ⊕-assoc one  one  c = sym (not-involutive c)

  ⊕-comm : (a b : 𝔽₂) → a ⊕ b ≡ b ⊕ a
  ⊕-comm zero zero = refl
  ⊕-comm zero one  = refl
  ⊕-comm one  zero = refl
  ⊕-comm one  one  = refl

  ⊕-self : (a : 𝔽₂) → a ⊕ a ≡ zero
  ⊕-self zero = refl
  ⊕-self one  = refl

  ∧-distribʳ-⊕ : (c a b : 𝔽₂) → (a ⊕ b) · c ≡ a · c ⊕ b · c
  ∧-distribʳ-⊕ c zero b    = refl
  ∧-distribʳ-⊕ c one  zero = sym (⊕-comm c zero)
  ∧-distribʳ-⊕ c one  one  = sym (⊕-self c)

  pow : (z : 𝔽₂) (n : ℕ) → z ^ (suc n) ≡ z
  pow z zero   = ∧-identityʳ z
  pow z (suc n) rewrite pow z n = ∧-idem z

