
-- (c) Davide Peressoni 2022

---------------------
-- Natural numbers --
---------------------

module Nat where
  open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+ℕ_) public
  open import Utils.Equality
  open import Ops

  instance
    Sumℕ : Sum ℕ
    _+_ ⦃ Sumℕ ⦄ = _+ℕ_
    additive-zero ⦃ Sumℕ ⦄ = 0
    lemma-sum-zero ⦃ Sumℕ ⦄ = refl

  lemma-nat-plus-zero : {a : ℕ} → a + 0 ≡ a
  lemma-nat-plus-zero {zero}  = refl
  lemma-nat-plus-zero {suc _} = cong suc lemma-nat-plus-zero

  lemma-nat-plus-suc : {a b : ℕ} → a + suc b ≡ suc (a + b)
  lemma-nat-plus-suc {0}     = refl
  lemma-nat-plus-suc {suc a} = cong suc lemma-nat-plus-suc

  instance
    Mulℕ : Mul ℕ
    _·_ ⦃ Mulℕ ⦄ = _*_
    unit ⦃ Mulℕ ⦄ = 1
    lemma-unit ⦃ Mulℕ ⦄ = lemma-nat-plus-zero

  open import Ring

  instance
    SumMonoidℕ : CommMonoid ℕ _+_ 0

    lemma-associative ⦃ SumMonoidℕ ⦄ {0}             = refl
    lemma-associative ⦃ SumMonoidℕ ⦄ {suc a} {b} {c} = cong suc (lemma-associative {a = a} {b = b} {c = c})

    lemma-commutative ⦃ SumMonoidℕ ⦄ {0}         = sym lemma-nat-plus-zero
    lemma-commutative ⦃ SumMonoidℕ ⦄ {suc a} {b} = trans (cong suc (lemma-commutative {a = a} {b = b})) (sym lemma-nat-plus-suc)

    lemma-identity-left ⦃ SumMonoidℕ ⦄ = refl


    MulMonoidℕ : CommMonoid ℕ _·_ 1

    lemma-associative ⦃ MulMonoidℕ ⦄ {0}                 = refl
    lemma-associative ⦃ MulMonoidℕ ⦄ {suc a} {0}         = lemma-associative {a = a} {b = 0}
    lemma-associative ⦃ MulMonoidℕ ⦄ {suc a} {suc b}     = {!   !}
    -- lemma-associative ⦃ MulMonoidℕ ⦄ {suc n} {suc m} {c} = trans (cong (_+_ c) (trans lemma-mul-right-distributive
    --                                                                                   (cong (_+_ (m * c)) (trans lemma-associative
    --                                                                                                             (cong (λ x → n · x) lemma-commutative)))))
    --                                                              lemma-associative

    lemma-commutative ⦃ MulMonoidℕ ⦄ {0}     {0}     = sym refl
    lemma-commutative ⦃ MulMonoidℕ ⦄ {0}     {suc b} = {!sym (lemma-commutative {a = b} {b = 0})!}
    lemma-commutative ⦃ MulMonoidℕ ⦄ {suc a} {0}     = {!lemma-commutative {a = a} {b = 0}!}
    lemma-commutative ⦃ MulMonoidℕ ⦄ {suc a} {suc b} = {!   !}

    lemma-identity-left ⦃ MulMonoidℕ ⦄ = lemma-identity-right


    Rigℕ : CommRig ℕ

    lemma-mul-left-distributive ⦃ Rigℕ ⦄ {0}             = refl
    lemma-mul-left-distributive ⦃ Rigℕ ⦄ {suc a} {b} {c} =  {!   !} --trans (trans (lemma-associative ⦃ SumMonoidℕ ⦄ {a = b} {b = c}) (cong (_+_ b) {!   !})) (sym lemma-associative)

    lemma-mul-zero-left ⦃ Rigℕ ⦄ = refl

