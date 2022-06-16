
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

---------------------
-- Integer numbers --
---------------------

module Data.Q where
  open import Data.Rational hiding (_+_ ; -_ ; _-_ ; _*_) public
  open import Data.Rational.Properties
  open import Data.Nat.Coprimality using (1-coprimeTo) renaming (sym to csym)
  open import Data.N as ℕ using (ℕ ; suc)
  open import Data.Int as ℤ using (ℤ ; 1ℤ)
  import Data.Integer.Properties as ℤp
  open import Utils

  ℤtoℚ : ℤ → ℚ
  ℤtoℚ z = z / 1

  -- ℤtoℚ-trans-≤ : {a b : ℤ} → a ℤ.≤ b → ℤtoℚ a ≤ ℤtoℚ b
  -- ℤtoℚ-trans-≤ {a} {b} p rewrite 1-coprimeTo ℤ.∣ a ∣ = *≤* {! p  !}

  ℕtoℚ : ℕ → ℚ
  ℕtoℚ n = ℤtoℚ (ℤ.pos n)

  ℕtoℚ-trans-≤ : {a b : ℕ} → a ℕ.≤ b → ℕtoℚ a ≤ ℕtoℚ b
  ℕtoℚ-trans-≤ {a} {b} p rewrite normalize-coprime (csym (1-coprimeTo a))
    | normalize-coprime (csym (1-coprimeTo b)) = *≤* (ℤp.*-monoʳ-≤-nonNeg 1 (ℤ.+≤+ p))

  2ℚ : ℚ
  2ℚ = ℕtoℚ 2

  ----------------
  -- Operations --
  ----------------

  open import Ops

  instance
    Sumℚ : Sum ℚ
    _+_ ⦃ Sumℚ ⦄ = Data.Rational._+_

    additive-zero ⦃ Sumℚ ⦄ = 0ℚ
    lemma-sum-zero ⦃ Sumℚ ⦄ = +-identityˡ _

  instance
    Subℚ : Sub ℚ
    -_ ⦃ Subℚ ⦄ = Data.Rational.-_

  instance
    Mulℚ : Mul ℚ
    _·_ ⦃ Mulℚ ⦄ = Data.Rational._*_

    unit ⦃ Mulℚ ⦄ = 1ℚ
    lemma-unit ⦃ Mulℚ ⦄ = *-identityˡ _

  open import Data.Integer.DivMod using (_div_)

  floor : ℚ → ℤ
  floor x = (↥ x) div (↧ x)

  ceil : ℚ → ℤ
  ceil x = - floor (- x)

  open import Relation.Binary.PropositionalEquality
  open import Data.Rational.Unnormalised.Base using (_≢0) public
  import Data.Nat.Properties as ℕp

  ------------------------
  -- Natural reciprocal --
  ------------------------

  infix 8 _⁻¹
  _⁻¹ : (n : ℕ) {_ : n ≢0} → ℚ
  _⁻¹ n {p} = _/_ 1ℤ n {p}

  _⁻¹⟨_⟩ : (n : ℕ) → n ≢0 → ℚ
  n ⁻¹⟨ p ⟩ = _⁻¹ n {p}

  ⁻¹≡ : (n : ℕ) → suc n ⁻¹ ≡ mkℚ 1ℤ n (1-coprimeTo (suc n))
  ⁻¹≡ n = normalize-coprime (1-coprimeTo (suc n))

  ≥⁻¹ : {n m : ℕ} {p : n ≢0} {q : m ≢0} → n ℕ.≥ m → n ⁻¹⟨ p ⟩ ≤ m ⁻¹⟨ q ⟩
  ≥⁻¹ (ℕ.s≤s {n} {m} r) rewrite ⁻¹≡ n | ⁻¹≡ m =
    *≤* (ℤ.+≤+ (ℕ.s≤s  (ℕp.+-mono-≤ r ℕ.z≤n)))

  ⁻¹-trans-suc : {n m : ℕ} → n ≡ m → suc n ⁻¹ ≡ suc m ⁻¹
  ⁻¹-trans-suc refl = refl

  ⁻¹-trans : {n m : ℕ} {p : n ≢0} {q : m ≢0} → n ≡ m → n ⁻¹⟨ p ⟩ ≡ m ⁻¹⟨ q ⟩
  ⁻¹-trans {suc n} refl = ⁻¹-trans-suc {n} refl

  --------------------
  -- Useful lemmas ---
  --------------------

  +-assoc-middle : (a b c d : ℚ) → (a + b) + (c + d) ≡ a + (b + c) + d
  +-assoc-middle = •-assoc-middle _+_ +-assoc

  +-comm-middle : (a b c d : ℚ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +-comm-middle = •-comm-middle _+_ +-comm +-assoc-middle

  lemma+- : (a b : ℚ) → a ≡ a + b - b
  lemma+- a b = begin
    a             ≡˘⟨ +-identityʳ a ⟩
    a + 0ℚ        ≡⟨ cong (_+_ a) (sym (+-inverseʳ b)) ⟩
    a + (b - b)   ≡˘⟨ +-assoc a b (- b) ⟩
    a + b + (- b) ∎
    where open ≡-Reasoning

  lemma-+ : (a b : ℚ) → a ≡ a - b + b
  lemma-+ a b =  begin
    a             ≡˘⟨ +-identityʳ a ⟩
    a + 0ℚ        ≡⟨ cong (_+_ a) (sym (+-inverseˡ b)) ⟩
    a + (- b + b) ≡˘⟨ +-assoc a (- b) b ⟩
    a + (- b) + b ∎
    where open ≡-Reasoning

  ∣a∣-∣b∣≤∣a-b∣ : (a b : ℚ) → ∣ a ∣ - ∣ b ∣ ≤ ∣ a - b ∣
  ∣a∣-∣b∣≤∣a-b∣ a b = begin
    ∣ a ∣ - ∣ b ∣             ≡⟨ cong (λ x → ∣ x ∣ - ∣ b ∣) (lemma-+ a b) ⟩
    ∣ a - b + b ∣ - ∣ b ∣     ≤⟨ +-monoˡ-≤ (- ∣ b ∣) (∣p+q∣≤∣p∣+∣q∣ (a - b) b) ⟩
    ∣ a - b ∣ + ∣ b ∣ - ∣ b ∣ ≡˘⟨ lemma+- ∣ a - b ∣ ∣ b ∣ ⟩
    ∣ a - b ∣                 ∎
    where open ≤-Reasoning


