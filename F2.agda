
-- (c) Davide Peressoni 2022

--------------------
-- Field modulo 2 --
--------------------

module F2 where
  open import Agda.Builtin.Bool renaming (Bool to 𝔽₂; false to zero; true to one) public
  open import Utils.Equality

  ¬ : 𝔽₂ → 𝔽₂
  ¬ zero = one
  ¬ one  = zero

  lemma-double-neg : {a : 𝔽₂} → ¬ (¬ a) ≡ a
  lemma-double-neg {zero} = refl
  lemma-double-neg {one}  = refl

  open import Ops

  instance
    open Sum ⦃ ... ⦄ renaming (_+_ to _⊕_) public
    Sum𝔽₂ : Sum 𝔽₂
    _⊕_ ⦃ Sum𝔽₂ ⦄ zero b = b
    _⊕_ ⦃ Sum𝔽₂ ⦄ one  b = ¬ b

    additive-zero ⦃ Sum𝔽₂ ⦄ = zero
    lemma-sum-zero ⦃ Sum𝔽₂ ⦄ = refl

  instance
    Mul𝔽₂ : Mul 𝔽₂
    _·_ ⦃ Mul𝔽₂ ⦄ zero _ = zero
    _·_ ⦃ Mul𝔽₂ ⦄ one  b = b

    unit ⦃ Mul𝔽₂ ⦄ = one
    lemma-unit ⦃ Mul𝔽₂ ⦄ = refl

  instance
    Sub𝔽₂ : Sub 𝔽₂
    -_ ⦃ Sub𝔽₂ ⦄ a = a


  open import Ring

  instance
    SumMonoid𝔽₂ : CommMonoid 𝔽₂ _+_ zero

    lemma-associative ⦃ SumMonoid𝔽₂ ⦄ {zero}       = refl
    lemma-associative ⦃ SumMonoid𝔽₂ ⦄ {one} {zero} = refl
    lemma-associative ⦃ SumMonoid𝔽₂ ⦄ {one} {one}  = sym lemma-double-neg

    lemma-commutative ⦃ SumMonoid𝔽₂ ⦄ {zero} {zero} = refl
    lemma-commutative ⦃ SumMonoid𝔽₂ ⦄ {zero} {one}  = refl
    lemma-commutative ⦃ SumMonoid𝔽₂ ⦄ {one}  {zero} = refl
    lemma-commutative ⦃ SumMonoid𝔽₂ ⦄ {one}  {one}  = refl

    lemma-identity-left ⦃ SumMonoid𝔽₂ ⦄ = refl


    MulMonoid𝔽₂ : CommMonoid 𝔽₂ _·_ one

    lemma-associative ⦃ MulMonoid𝔽₂ ⦄ {zero} = refl
    lemma-associative ⦃ MulMonoid𝔽₂ ⦄ {one}  = refl

    lemma-commutative ⦃ MulMonoid𝔽₂ ⦄ {zero} {zero} = refl
    lemma-commutative ⦃ MulMonoid𝔽₂ ⦄ {zero} {one}  = refl
    lemma-commutative ⦃ MulMonoid𝔽₂ ⦄ {one}  {zero} = refl
    lemma-commutative ⦃ MulMonoid𝔽₂ ⦄ {one}  {one}  = refl

    lemma-identity-left ⦃ MulMonoid𝔽₂ ⦄ = refl


    Rig𝔽₂ : CommRig 𝔽₂

    lemma-mul-left-distributive ⦃ Rig𝔽₂ ⦄ {zero} = refl
    lemma-mul-left-distributive ⦃ Rig𝔽₂ ⦄ {one}  = refl

    lemma-mul-zero-left ⦃ Rig𝔽₂ ⦄ = refl


    Ring𝔽₂ : CommRing 𝔽₂

    lemma-additive-inverse ⦃ Ring𝔽₂ ⦄ {zero} = refl
    lemma-additive-inverse ⦃ Ring𝔽₂ ⦄ {one}  = refl

