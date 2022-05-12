
-- (c) Davide Peressoni 2022

module Data.F2.Properties where
  open import Data.Bool.Properties public

  open import Relation.Binary.PropositionalEquality
  open import Data.F2

  ⊕-assoc : (a : 𝔽₂) → (b : 𝔽₂) → (c : 𝔽₂) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
  ⊕-assoc zero _    _ = refl
  ⊕-assoc one  zero _ = refl
  ⊕-assoc one  one  c = sym (not-involutive c)

  ⊕-comm : (a : 𝔽₂) → (b : 𝔽₂) → a ⊕ b ≡ b ⊕ a
  ⊕-comm zero zero = refl
  ⊕-comm zero one  = refl
  ⊕-comm one  zero = refl
  ⊕-comm one  one  = refl

  ⊕-self : (a : 𝔽₂) → a ⊕ a ≡ zero
  ⊕-self zero = refl
  ⊕-self one  = refl
