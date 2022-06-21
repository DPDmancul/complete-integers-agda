
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

---------------
-- Utilities --
---------------

module Utils where
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import Data.Empty
  open import Function.Base

  transport : {A : Set} {x y : A} → (f : A → Set) → x ≡ y → f x → f y
  transport f refl s = s

  •-assoc-middle : {A : Set} → (_•_ : A → A → A) →
    (•-assoc : (a b c : A) → (a • b) • c ≡ a • (b • c)) →
    (a b c d : A) → ((a • b) • (c • d)) ≡ (a • (b • c)) • d
  •-assoc-middle _•_ •-assoc a b c d = begin
      (a • b) • (c • d) ≡˘⟨ •-assoc (a • b) c d ⟩
      ((a • b) • c) • d ≡⟨ cong (_• d) (•-assoc a b c) ⟩
      (a • (b • c)) • d ∎

  •-comm-middle : {A : Set} → (_•_ : A → A → A) →
    (•-comm : (a b : A) → (a • b) ≡ (b • a)) →
    (•-assoc-middle : (a b c d : A) →
      ((a • b) • (c • d)) ≡ (a • (b • c)) • d) →
    (a b c d : A) → (a • b) • (c • d) ≡ (a • c) • (b • d)
  •-comm-middle _•_ •-comm •-assoc-middle a b c d = begin
    (a • b) • (c • d) ≡⟨ •-assoc-middle a b c d ⟩
    (a • (b • c)) • d ≡⟨ cong (λ x → (a • x) • d) (•-comm b c) ⟩
    (a • (c • b)) • d ≡˘⟨ •-assoc-middle a c b d ⟩
    (a • c) • (b • d) ∎

  •-inverse-middleˡ : {A : Set} → (_•_ : A → A → A) → (-_ : A → A) → (0# : A) →
    (•-assoc : (a b c : A) → (a • b) • c ≡ a • (b • c)) →
    (•-inverseˡ : (a : A) → (- a) • a ≡ 0#) →
    (•-identityʳ : (a : A) → a • 0# ≡ a) →
    (a b c : A) → (a • (- b)) • (b • c) ≡ a • c
  •-inverse-middleˡ _•_ -_ 0# •-assoc •-inverseˡ •-identityʳ a b c =
    begin
    (a • (- b)) • (b • c) ≡˘⟨ •-assoc (a • (- b)) b c ⟩
    ((a • (- b)) • b) • c ≡⟨ (cong (_• c) $ •-assoc a (- b) b) ⟩
    (a • ((- b) • b)) • c ≡⟨ (cong (λ x → (a • x) • c) $ •-inverseˡ b) ⟩
    (a • 0#) • c          ≡⟨ (cong (_• c) $ •-identityʳ a) ⟩
    a • c                 ∎

  ⊥-irrelevant : .⊥ → ⊥
  ⊥-irrelevant ()

