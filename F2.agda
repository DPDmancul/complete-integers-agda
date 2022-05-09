
-- (c) Davide Peressoni 2022

--------------------
-- Field modulo 2 --
--------------------

module F2 where
  open import Agda.Builtin.Bool renaming (Bool to 𝔽₂; false to zero; true to one) public
  open import Agda.Builtin.Equality

  ¬ : 𝔽₂ → 𝔽₂
  ¬ zero = one
  ¬ one  = zero

  open import Ops

  instance
    open Sum ⦃ ... ⦄ renaming (_+_ to _⊕_) public
    Sum𝔽₂ : Sum 𝔽₂
    _⊕_ ⦃ Sum𝔽₂ ⦄ zero b = b
    _⊕_ ⦃ Sum𝔽₂ ⦄ one  b = ¬ b
    additive-zero ⦃ Sum𝔽₂ ⦄ = zero
    lemma-sum-zero ⦃ Sum𝔽₂ ⦄ x = refl

  instance
    Mul𝔽₂ : Mul 𝔽₂
    _·_ ⦃ Mul𝔽₂ ⦄ zero _ = zero
    _·_ ⦃ Mul𝔽₂ ⦄ one  b = b
    unit ⦃ Mul𝔽₂ ⦄ = one
    lemma-unit ⦃ Mul𝔽₂ ⦄ x = refl

