
-- (c) Davide Peressoni 2022

---------------------------
-- Even and Odd integers --
---------------------------

module Even where
  open import Data.N
  open import Data.Int
  import Data.Integer.Properties as ℤp
  open import Data.Bool
  open import Data.Empty
  open import Ops
  open import Utils
  open import Relation.Binary.PropositionalEquality

  2ℤ : ℤ
  2ℤ = 1ℤ + 1ℤ

  data Even : ℤ → Set where
    base : Even 0ℤ
    step : {z : ℤ} → Even z → Even (2ℤ + z)
    pets : {z : ℤ} → Even z → Even (- 2ℤ + z)

  data Odd : ℤ → Set where
    base : Odd 1ℤ
    step : {z : ℤ} → Odd z → Odd (2ℤ + z)
    pets : {z : ℤ} → Odd z → Odd (- 2ℤ + z)

  data EvenOrOdd (z : ℤ) : Set where
    even : Even z → EvenOrOdd z
    odd  : Odd  z → EvenOrOdd z

  ------------
  -- Lemmas --
  ------------

  suc-even : {z : ℤ} → Even z → Odd (1ℤ + z)
  suc-even base         = base
  suc-even (step {z} p) = transport
    Odd
    (trans (sym (ℤp.+-assoc 2ℤ 1ℤ z))
           (trans (cong (λ x → x + z) (ℤp.+-comm 2ℤ 1ℤ))
                  (ℤp.+-assoc 1ℤ 2ℤ z)))
    (step (suc-even p))
  suc-even (pets {z} p) = transport
    Odd
    (trans (sym (ℤp.+-assoc -[1+ 1 ] 1ℤ z))
           (trans (cong (λ x → x + z) (ℤp.+-comm -[1+ 1 ] 1ℤ))
                  (ℤp.+-assoc 1ℤ -[1+ 1 ] z)))
    (pets (suc-even p))


  ------------------
  -- Cast to Bool --
  ------------------

  private
    helper-even? : (z : ℤ) → EvenOrOdd z → Bool
    helper-even? _ (even _) = true
    helper-even? _ (odd  _) = false

  even? : ℤ → Bool
  even? z@(ℤ.pos zero) = helper-even? z (even base)
  even? z@(+[1+ _ ]) = helper-even? z {!   !}
  even? z@(-[1+ _ ]) = helper-even? z {!   !}

  odd? : ℤ → Bool
  odd? z = not (even? z)

