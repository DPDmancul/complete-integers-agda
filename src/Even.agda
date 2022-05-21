
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

  private
    helper-suc : (x : ℤ) → (y : ℤ) → (z : ℤ)
      → (A : ℤ → Set) → A (x + (y + z)) → A (y + (x + z))
    helper-suc x y z A = transport A
      (trans (sym (ℤp.+-assoc x y z))
             (trans (cong (λ z' → z' + z) (ℤp.+-comm x y))
                    (ℤp.+-assoc y x z)))

  suc-even : {z : ℤ} → Even z → Odd (1ℤ + z)
  suc-even base         = base
  suc-even (step {z} p) = helper-suc 2ℤ 1ℤ z Odd (step (suc-even p))
  suc-even (pets {z} p) = helper-suc -[1+ 1 ] 1ℤ z Odd (pets (suc-even p))

  suc-odd : {z : ℤ} → Odd z → Even (1ℤ + z)
  suc-odd base         = step base
  suc-odd (step {z} p) = helper-suc 2ℤ 1ℤ z Even (step (suc-odd p))
  suc-odd (pets {z} p) = helper-suc -[1+ 1 ] 1ℤ z Even (pets (suc-odd p))

  pred-even : {z : ℤ} → Even z → Odd (- 1ℤ + z)
  pred-even {z} p rewrite ℤp.+-assoc 1ℤ (- 2ℤ) z = suc-even (pets p)

  pred-odd : {z : ℤ} → Odd z → Even (- 1ℤ + z)
  pred-odd {z} p rewrite ℤp.+-assoc 1ℤ (- 2ℤ) z = suc-odd (pets p)

  neg-even : {z : ℤ} → Even z → Even (- z)
  neg-even base = base
  neg-even (step {z} p) rewrite ℤp.neg-distrib-+ 2ℤ z = pets (neg-even p)
  neg-even (pets {z} p) rewrite ℤp.neg-distrib-+ -[1+ 1 ] z = step (neg-even p)

  ------------------
  -- Cast to Bool --
  ------------------

  even-or-odd : (z : ℤ) → EvenOrOdd z
  even-or-odd (ℤ.pos 0) = even base
  even-or-odd (+[1+ n ]) with even-or-odd (ℤ.pos n)
  ... | even p = odd (suc-even p)
  ... | odd  p = even (suc-odd p)
  even-or-odd -[1+ 0 ] = odd (pets base)
  even-or-odd -[1+ ℕ.suc n ] with even-or-odd -[1+ n ]
  ... | even p = odd (pred-even p)
  ... | odd  p = even (pred-odd p)

  -- lemma-even : {z : ℤ} → (p : Even z) → even-or-odd z ≡ even p
  -- lemma-even {ℤ.pos  0} p = {!   !}
  -- lemma-even { +[1+ n ] } p = {!   !}
  -- lemma-even { -[1+ n ] } p = {!   !}

  even? : ℤ → Bool
  even? z with even-or-odd z
  ... | even _ = true
  ... | odd  _ = false

  odd? : ℤ → Bool
  odd? z = not (even? z)

