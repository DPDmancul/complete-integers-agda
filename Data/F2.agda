
-- (c) Davide Peressoni 2022

--------------------
-- Field modulo 2 --
--------------------

module Data.F2 where
  import Data.Bool renaming (Bool to 𝔽₂; false to zero; true to one ; not to ¬)
  open Data.Bool using (𝔽₂ ; zero ; one ; ¬) public

  open import Agda.Builtin.Equality

  open import Ops

  instance
    open Sum ⦃ ... ⦄ using () renaming (_+_ to _⊕_) public
    Sum𝔽₂ : Sum 𝔽₂
    _⊕_ ⦃ Sum𝔽₂ ⦄ = Data.Bool._xor_

    additive-zero ⦃ Sum𝔽₂ ⦄ = zero
    lemma-sum-zero ⦃ Sum𝔽₂ ⦄ = refl

  instance
    Mul𝔽₂ : Mul 𝔽₂
    _*_ ⦃ Mul𝔽₂ ⦄ = Data.Bool._∧_

    unit ⦃ Mul𝔽₂ ⦄ = one
    lemma-unit ⦃ Mul𝔽₂ ⦄ = refl

  instance
    Sub𝔽₂ : Sub 𝔽₂
    -_ ⦃ Sub𝔽₂ ⦄ a = a

