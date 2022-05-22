
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

  neg-odd : {z : ℤ} → Odd z → Odd (- z)
  neg-odd base = pets base
  neg-odd (step {z} p) rewrite ℤp.neg-distrib-+ 2ℤ z = pets (neg-odd p)
  neg-odd (pets {z} p) rewrite ℤp.neg-distrib-+ -[1+ 1 ] z = step (neg-odd p)

  ----------------------------------------------------------------------------

  sum-even-even : {x y : ℤ} → Even x → Even y → Even (x + y)
  sum-even-even {y = y} base q rewrite lemma-sum-zero {ℤ} {y} = q
  sum-even-even {y = y} (step {z} p) q = transport Even
      (sym (ℤp.+-assoc 2ℤ z y))
      (step (sum-even-even p q))
  sum-even-even {y = y} (pets {z} p) q = transport Even
      (sym (ℤp.+-assoc -[1+ 1 ] z y))
      (pets (sum-even-even p q))

  sum-odd-odd : {x y : ℤ} → Odd x → Odd y → Even (x + y)
  sum-odd-odd         base         q = suc-odd q
  sum-odd-odd {y = y} (step {z} p) q = transport Even
      (sym (ℤp.+-assoc 2ℤ z y))
      (step (sum-odd-odd p q))
  sum-odd-odd {y = y} (pets {z} p) q = transport Even
      (sym (ℤp.+-assoc -[1+ 1 ] z y))
      (pets (sum-odd-odd p q))

  sum-odd-even : {x y : ℤ} → Odd x → Even y → Odd (x + y)
  sum-odd-even         base         q = suc-even q
  sum-odd-even {y = y} (step {z} p) q = transport Odd
      (sym (ℤp.+-assoc 2ℤ z y))
      (step (sum-odd-even p q))
  sum-odd-even {y = y} (pets {z} p) q = transport Odd
      (sym (ℤp.+-assoc -[1+ 1 ] z y))
      (pets (sum-odd-even p q))

  sum-even-odd : {x y : ℤ} → Even x → Odd y → Odd (x + y)
  sum-even-odd {x} {y} p q rewrite ℤp.+-comm x y = sum-odd-even q p

  ----------------------------------------------------------------------------

  private
    double-even-ℕ : (n : ℕ) → Even (ℤ.pos (n · 2))
    double-even-ℕ zero      = base
    double-even-ℕ (ℕ.suc n) = step (double-even-ℕ n)

    neg-double-even-ℕ : (n : ℕ) → Even -[1+ ℕ.suc (n · 2)]
    neg-double-even-ℕ zero = pets base
    neg-double-even-ℕ (ℕ.suc n) = pets (neg-double-even-ℕ n)

  double-even : {z : ℤ} → Even (2ℤ · z)
  double-even {ℤ.pos zero} = base
  double-even { +[1+ n ] } rewrite ℤp.*-comm 2ℤ +[1+ n ] =
    step (double-even-ℕ n)
  double-even { -[1+ n ] } rewrite ℤp.*-comm 2ℤ -[1+ n ] =
    neg-double-even-ℕ n

  neg-double-even : {z : ℤ} → Even (- 2ℤ · z)
  neg-double-even {z} rewrite sym (ℤp.neg-distribˡ-* 2ℤ z) =
    neg-even (double-even {z})

  ----------------------------------------------------------------------------

  mul-even-even : {x y : ℤ} → Even x → Even y → Even (x · y)
  mul-even-even base _ = base
  mul-even-even {y = y} (step {z} p) q rewrite ℤp.*-distribʳ-+ y 2ℤ z =
    sum-even-even (double-even {y}) (mul-even-even p q)
  mul-even-even {y = y} (pets {z} p) q rewrite ℤp.*-distribʳ-+ y -[1+ 1 ] z =
    sum-even-even (neg-double-even {y}) (mul-even-even p q)

  mul-odd-odd : {x y : ℤ} → Odd x → Odd y → Odd (x · y)
  mul-odd-odd {y = y} base q rewrite lemma-unit {ℤ} {y} = q
  mul-odd-odd {y = y} (step {z} p) q rewrite ℤp.*-distribʳ-+ y 2ℤ z
    = sum-even-odd (double-even {y}) (mul-odd-odd p q)
  mul-odd-odd {y = y} (pets {z} p) q rewrite ℤp.*-distribʳ-+ y -[1+ 1 ] z =
    sum-even-odd (neg-double-even {y}) (mul-odd-odd p q)

  mul-even-odd : {x y : ℤ} → Even x → Odd y → Even (x · y)
  mul-even-odd base q = base
  mul-even-odd {y = y} (step {z} p) q rewrite ℤp.*-distribʳ-+ y 2ℤ z =
    sum-even-even (double-even {y}) (mul-even-odd p q)
  mul-even-odd {y = y} (pets {z} p) q rewrite ℤp.*-distribʳ-+ y -[1+ 1 ] z =
    sum-even-even (neg-double-even {y}) (mul-even-odd p q)

  mul-odd-even : {x y : ℤ} → Odd x → Even y → Even (x · y)
  mul-odd-even {x} {y} p q rewrite ℤp.*-comm x y = mul-even-odd q p

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

  postulate
    -- Since the constructors of Even and Odd don't take constructors of ℤ as
    -- parameters it is impossible for Agda to prove there is no constructor for
    -- Odd 0ℤ and Even (- 1ℤ).
    lemma-even : {z : ℤ} → (p : Even z) → even-or-odd z ≡ even p
    lemma-odd  : {z : ℤ} → (p : Odd  z) → even-or-odd z ≡ odd  p

  even? : ℤ → Bool
  even? z with even-or-odd z
  ... | even _ = true
  ... | odd  _ = false

  odd? : ℤ → Bool
  odd? z = not (even? z)

