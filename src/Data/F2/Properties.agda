
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

----------------------------------
-- Properties of field modulo 2 --
----------------------------------

module Data.F2.Properties where
  open import Data.Bool.Properties public

  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import Data.F2
  open import Data.N
  open import Ops

  ¬-double : (a : 𝔽₂) → ¬ (¬ a) ≡ a
  ¬-double zero = refl
  ¬-double one = refl

  ⊕-assoc : (a b c : 𝔽₂) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
  ⊕-assoc zero _    _ = refl
  ⊕-assoc one  zero _ = refl
  ⊕-assoc one  one  c = sym (not-involutive c)

  ⊕-comm : (a b : 𝔽₂) → a ⊕ b ≡ b ⊕ a
  ⊕-comm zero zero = refl
  ⊕-comm zero one  = refl
  ⊕-comm one  zero = refl
  ⊕-comm one  one  = refl

  ⊕-assoc-middle : (a b c d : 𝔽₂) → (a ⊕ b) ⊕ (c ⊕ d) ≡ a ⊕ (b ⊕ c) ⊕ d
  ⊕-assoc-middle a b c d =  begin
    (a ⊕ b) ⊕ (c ⊕ d) ≡⟨ ⊕-assoc a b (c ⊕ d) ⟩
    a ⊕ (b ⊕ (c ⊕ d)) ≡⟨ cong (_⊕_ a) (sym (⊕-assoc b c d)) ⟩
    a ⊕ ((b ⊕ c) ⊕ d) ≡⟨ sym (⊕-assoc a (b ⊕ c) d) ⟩
    a ⊕ (b ⊕ c) ⊕ d    ∎

  ⊕-comm-middle : (a b c d : 𝔽₂) → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
  ⊕-comm-middle a b c d =  begin
    (a ⊕ b) ⊕ (c ⊕ d) ≡⟨ ⊕-assoc-middle a b c d ⟩
    a ⊕ (b ⊕ c) ⊕ d   ≡⟨ cong (λ x → a ⊕ x ⊕ d) (⊕-comm b c) ⟩
    a ⊕ (c ⊕ b) ⊕ d   ≡⟨ sym (⊕-assoc-middle a c b d) ⟩
    (a ⊕ c) ⊕ (b ⊕ d) ∎

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

  ¬-distribˡ-⊕ : (a b : 𝔽₂) → ¬ (a ⊕ b) ≡ (¬ a) ⊕ b
  ¬-distribˡ-⊕ zero b = refl
  ¬-distribˡ-⊕ one  b = ¬-double b

  ¬-distribʳ-⊕ : (a b : 𝔽₂) → ¬ (a ⊕ b) ≡ a ⊕ (¬ b)
  ¬-distribʳ-⊕ zero b = refl
  ¬-distribʳ-⊕ one  b = refl

  ¬-distrib-⊕ : (a b : 𝔽₂) → (¬ a) ⊕ (¬ b) ≡ a ⊕ b
  ¬-distrib-⊕ zero b = ¬-double b
  ¬-distrib-⊕ one  b = refl

