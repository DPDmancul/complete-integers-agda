
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

---------------
-- Utilities --
---------------

module Utils where
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning

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
