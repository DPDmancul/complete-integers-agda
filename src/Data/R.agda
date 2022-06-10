
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe #-}

------------------
-- Real numbers --
------------------

module Data.R where
  open import Data.N hiding (_≤_ ; ∣_-_∣)
  open import Data.Int using (1ℤ)
  open import Data.Q
  import Data.Rational.Properties as ℚp
  open import Relation.Binary.PropositionalEquality

  open import Ops

  record ℝ : Set where
    field
      seq : ℕ → ℚ
      .conv : {n m : ℕ} → ∣ seq n - seq m ∣ ≤ 1ℤ / suc n + 1ℤ / suc m

  fromℚ : ℚ → ℝ
  ℝ.seq  (fromℚ q) _       = q
  -- ℝ.conv (fromℚ q) rewrite ℚp.+-inverseʳ q = ℚp.nonNegative⁻¹ {! ℚp.+-mono-≤ {0ℚ} {_} {0ℚ} ? ?  !}
  ℝ.conv (fromℚ q) {n} {m} = begin
    ∣ q - q ∣       ≡⟨ cong ∣_∣ (ℚp.+-inverseʳ q) ⟩
    0ℚ              ≤⟨ ℚp.nonNegative⁻¹ (ℚp.normalize-nonNeg 1 (suc m)) ⟩
    1ℤ / suc m      ≡⟨ sym (ℚp.+-identityˡ (1ℤ / suc m)) ⟩
    0ℚ + 1ℤ / suc m ≤⟨ ℚp.+-monoˡ-≤ (1ℤ / suc m)
      (ℚp.nonNegative⁻¹ {1ℤ / suc n} (ℚp.normalize-nonNeg 1 (suc n))) ⟩
    1ℤ / suc n + 1ℤ / suc m ∎
    where open ℚp.≤-Reasoning

  0ℝ : ℝ
  0ℝ = fromℚ 0ℚ

  1ℝ : ℝ
  1ℝ = fromℚ 1ℚ


