
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

---------------------
-- Integer numbers --
---------------------

module Data.Q where
  open import Data.Rational hiding (_+_ ; -_ ; _-_ ; _*_) public
  open import Data.Rational.Properties
  open import Data.N as ℕ using (ℕ ; suc)
  open import Data.Int as ℤ using (ℤ ; 1ℤ)

  ℤtoℚ : ℤ → ℚ
  ℤtoℚ z = z / 1

  ℕtoℚ : ℕ → ℚ
  ℕtoℚ n = ℤtoℚ (ℤ.pos n)

  2ℚ : ℚ
  2ℚ = ℕtoℚ 2

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


  open import Relation.Binary.PropositionalEquality
  open import Data.Rational.Unnormalised.Base using (_≢0) public
  open import Data.Nat.Coprimality using (1-coprimeTo)
  import Data.Nat.Properties as ℕp

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

  +-assoc-middle : (a b c d : ℚ) → (a + b) + (c + d) ≡ a + (b + c) + d
  +-assoc-middle a b c d = begin
    a + b + (c + d) ≡⟨ sym (+-assoc (a + b) c d) ⟩
    (a + b + c) + d ≡⟨ cong (_+ d) (+-assoc a b c) ⟩
    a + (b + c) + d ∎
    where open ≡-Reasoning

  +-comm-middle : (a b c d : ℚ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +-comm-middle a b c d = begin
    (a + b) + (c + d) ≡⟨ +-assoc-middle a b c d ⟩
    a + (b + c) + d   ≡⟨ cong (λ x → a + x + d) (+-comm b c) ⟩
    a + (c + b) + d   ≡⟨ sym (+-assoc-middle a c b d) ⟩
    (a + c) + (b + d) ∎
    where open ≡-Reasoning

  open import Data.Integer.DivMod using (_div_)

  floor : ℚ → ℤ
  floor x = (↥ x) div (↧ x)

  ceil : ℚ → ℤ
  ceil x = - floor (- x)

