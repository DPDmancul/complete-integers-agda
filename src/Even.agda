
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

---------------------------
-- Even and Odd integers --
---------------------------

module Even where
  open import Data.N
  open import Data.Int
  import Data.Nat.Properties as ℕp
  import Data.Integer.Properties as ℤp
  open import Data.Bool
  open import Data.Empty
  open import Ops
  open import Utils
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import Function.Base

  data Even : ℤ → Set where
    base : Even 0ℤ
    step : {n : ℕ} → Even (ℤ.pos n) → Even +[1+ ℕ.suc n ]
    pets : {n : ℕ} → Even (ℤ.pos n) → Even -[1+ ℕ.suc n ]

  data Odd : ℤ → Set where
    base : Odd 1ℤ
    esab : Odd (- 1ℤ)
    step : {n : ℕ} → Odd (ℤ.pos n) → Odd +[1+ ℕ.suc n ]
    pets : {n : ℕ} → Odd (ℤ.pos n) → Odd -[1+ ℕ.suc n ]

  data EvenOrOdd (z : ℤ) : Set where
    even : Even z → EvenOrOdd z
    odd  : Odd  z → EvenOrOdd z

  ------------
  -- Lemmas --
  ------------

  neg-even : {z : ℤ} → Even z → Even (- z)
  neg-even base     = base
  neg-even (step p) = pets p
  neg-even (pets p) = step p

  neg-odd : {z : ℤ} → Odd z → Odd (- z)
  neg-odd base     = esab
  neg-odd esab     = base
  neg-odd (step p) = pets p
  neg-odd (pets p) = step p

  private
    helper-suc : (n : ℕ) → (A : ℤ → Set) →
      A (2ℤ + (1ℤ + ℤ.pos n)) → A (1ℤ + (2ℤ + ℤ.pos n))
    helper-suc n A = transport A $
      trans (sym $ ℤp.+-assoc 2ℤ 1ℤ $ ℤ.pos n)
             (trans (cong (λ z → z + ℤ.pos n) $ ℤp.+-comm 2ℤ 1ℤ)
                    (ℤp.+-assoc 1ℤ 2ℤ $ ℤ.pos n))

  suc-even : {z : ℤ} → Even z → Odd (1ℤ + z)
  suc-even base         = base
  suc-even (step {n} p) = helper-suc n Odd (step (suc-even p))
  suc-even (pets     p) = neg-odd (suc-even p)

  suc-odd : {z : ℤ} → Odd z → Even (1ℤ + z)
  suc-odd base         = step base
  suc-odd esab         = base
  suc-odd (step {n} p) = helper-suc n Even (step (suc-odd p))
  suc-odd (pets {z} p) = neg-even (suc-odd p)

  pred-even : {z : ℤ} → Even z → Odd (-1ℤ + z)
  pred-even base = esab
  pred-even (step {n} p) = suc-even p
  pred-even (pets     p) = neg-odd (suc-even (suc-odd (suc-even p)))

  pred-odd : {z : ℤ} → Odd z → Even (-1ℤ + z)
  pred-odd base = base
  pred-odd esab = pets base
  pred-odd (step {n} p) = suc-odd p
  pred-odd (pets     p) = neg-even (suc-odd (suc-even (suc-odd p)))

  ----------------------------------------------------------------------------

  sum-even-even : {x y : ℤ} → Even x → Even y → Even (x + y)
  sum-even-even {y = y} base q rewrite ℤp.+-identityˡ y = q
  sum-even-even {y = y} (step {n} p) q
    rewrite ℤp.+-assoc 2ℤ (ℤ.pos n) y | ℤp.+-assoc 1ℤ 1ℤ ((ℤ.pos n) + y) =
      suc-odd (suc-even (sum-even-even p q))
  sum-even-even (pets {n} p) base = pets p
  sum-even-even (pets {n} p) (step {m} q)
    rewrite ℤp.[1+m]⊖[1+n]≡m⊖n (ℕ.suc m) (ℕ.suc n) | ℤp.[1+m]⊖[1+n]≡m⊖n m n
    | sym (ℤp.-m+n≡n⊖m n m) =
      sum-even-even (neg-even p) q
  sum-even-even (pets {n} p) (pets {m} q)
    rewrite ℕp.+-comm n (ℕ.suc m) | ℕp.+-comm m n =
      pets (step (sum-even-even p q))

  private
    1+-1 : (x y : ℤ) → x + y ≡ 1ℤ + ((-1ℤ + x) + y)
    1+-1 x y =  begin
      x + y                ≡˘⟨ ℤp.+-identityˡ (x + y) ⟩
      0ℤ + (x + y)         ≡⟨ ℤp.+-assoc 1ℤ -1ℤ (x + y) ⟩
      1ℤ + (-1ℤ + (x + y)) ≡⟨ cong (_+_ 1ℤ) (sym (ℤp.+-assoc -1ℤ x y)) ⟩
      1ℤ + ((-1ℤ + x) + y) ∎

  sum-odd-even : {x y : ℤ} → Odd x → Even y → Odd (x + y)
  sum-odd-even {y = y} base q = suc-even q
  sum-odd-even {x} {y} p q rewrite 1+-1 x y =
      sum-odd-even base (sum-even-even (pred-odd p) q)

  sum-even-odd : {x y : ℤ} → Even x → Odd y → Odd (x + y)
  sum-even-odd {x} {y} p q rewrite ℤp.+-comm x y = sum-odd-even q p

  sum-odd-odd : {x y : ℤ} → Odd x → Odd y → Even (x + y)
  sum-odd-odd base q = suc-odd q
  sum-odd-odd {x} {y} p q rewrite 1+-1 x y =
      sum-odd-odd base (sum-even-odd (pred-odd p) q)

  ----------------------------------------------------------------------------

  private
    double-even-ℕ : (n : ℕ) → Even (ℤ.pos (n · 2))
    double-even-ℕ 0         = base
    double-even-ℕ (ℕ.suc n) = step (double-even-ℕ n)

    neg-double-even-ℕ : (n : ℕ) → Even -[1+ ℕ.suc (n · 2)]
    neg-double-even-ℕ 0         = pets base
    neg-double-even-ℕ (ℕ.suc n) = pets (suc-odd (suc-even (double-even-ℕ n)))

  double-even : {z : ℤ} → Even (2ℤ · z)
  double-even {ℤ.pos 0} = base
  double-even { +[1+ n ] } rewrite ℤp.*-comm 2ℤ +[1+ n ] =
    step (double-even-ℕ n)
  double-even { -[1+ n ] } rewrite ℤp.*-comm 2ℤ -[1+ n ] =
    neg-double-even-ℕ n

  ----------------------------------------------------------------------------

  private
    -[1+n]·y≡-[2y+ny] : (n : ℕ) → (y : ℤ) → -[1+ ℕ.suc n ] · y ≡ -(2ℤ · y + (ℤ.pos n) · y )
    -[1+n]·y≡-[2y+ny] n y = begin
      -[1+ ℕ.suc n ] · y         ≡˘⟨ ℤp.neg-distribˡ-* +[1+ ℕ.suc n ] y ⟩
      -(+[1+ ℕ.suc n ] · y)      ≡⟨ cong -_ (ℤp.*-distribʳ-+ y +[1+ 1 ] (ℤ.pos n)) ⟩
      -(2ℤ · y + (ℤ.pos n) · y ) ∎

  mul-even-even : {x y : ℤ} → Even x → Even y → Even (x · y)
  mul-even-even base _ = base
  mul-even-even {y = y} (step {n} p) q rewrite ℤp.*-distribʳ-+ y 2ℤ (ℤ.pos n) =
    sum-even-even (double-even {y}) (mul-even-even p q)
  mul-even-even {y = y} (pets {n} p) q rewrite -[1+n]·y≡-[2y+ny] n y =
    neg-even (sum-even-even (double-even {y}) (mul-even-even p q))

  mul-odd-odd : {x y : ℤ} → Odd x → Odd y → Odd (x · y)
  mul-odd-odd {y = y} base q rewrite ℤp.*-identityˡ y = q
  mul-odd-odd {y = y} esab q
    rewrite sym (ℤp.neg-distribˡ-* 1ℤ y) | ℤp.*-identityˡ y =
      neg-odd q
  mul-odd-odd {y = y} (step {n} p) q rewrite ℤp.*-distribʳ-+ y 2ℤ (ℤ.pos n) =
    sum-even-odd (double-even {y}) (mul-odd-odd p q)
  mul-odd-odd {y = y} (pets {n} p) q rewrite -[1+n]·y≡-[2y+ny] n y =
    neg-odd (sum-even-odd (double-even {y}) (mul-odd-odd p q))

  mul-even-odd : {x y : ℤ} → Even x → Odd y → Even (x · y)
  mul-even-odd base q = base
  mul-even-odd {y = y} (step {n} p) q rewrite ℤp.*-distribʳ-+ y 2ℤ (ℤ.pos n) =
    sum-even-even (double-even {y}) (mul-even-odd p q)
  mul-even-odd {y = y} (pets {n} p) q rewrite -[1+n]·y≡-[2y+ny] n y =
    neg-even (sum-even-even (double-even {y}) (mul-even-odd p q))

  mul-odd-even : {x y : ℤ} → Odd x → Even y → Even (x · y)
  mul-odd-even {x} {y} p q rewrite ℤp.*-comm x y = mul-even-odd q p

  -- ------------------
  -- -- Cast to Bool --
  -- ------------------

  even-or-odd : (z : ℤ) → EvenOrOdd z
  even-or-odd (ℤ.pos 0)  = even base
  even-or-odd (+[1+ 0 ]) = odd base
  even-or-odd (+[1+ ℕ.suc n ]) with even-or-odd +[1+ n ]
  ... | even p = odd (suc-even p)
  ... | odd  p = even (suc-odd p)
  even-or-odd -[1+ 0 ] = odd esab
  even-or-odd -[1+ ℕ.suc n ] with even-or-odd -[1+ n ]
  ... | even p = odd (pred-even p)
  ... | odd  p = even (pred-odd p)

  uniq-cert-even : {z : ℤ} → (p q : Even z) → p ≡ q
  uniq-cert-even base base         = refl
  uniq-cert-even (step p) (step q) = cong step (uniq-cert-even p q)
  uniq-cert-even (pets p) (pets q) = cong pets (uniq-cert-even p q)

  uniq-cert-odd : {z : ℤ} → (p q : Odd z) → p ≡ q
  uniq-cert-odd base base         = refl
  uniq-cert-odd esab esab         = refl
  uniq-cert-odd (step p) (step q) = cong step (uniq-cert-odd p q)
  uniq-cert-odd (pets p) (pets q) = cong pets (uniq-cert-odd p q)

  assert-evenness : {z : ℤ} → (p : EvenOrOdd z) → even-or-odd z ≡ p
  assert-evenness {ℤ.pos 0}    (even base) = refl
  assert-evenness { +[1+ 0 ] } (odd base)  = refl
  assert-evenness { -[1+ 0 ] } (odd esab)  = refl
  assert-evenness {+[1+ ℕ.suc n ]} (even (step p))
    rewrite assert-evenness {+[1+ n ]} (odd (suc-even p)) =
      cong even $ uniq-cert-even (suc-odd (suc-even p)) (step p)
  assert-evenness {+[1+ ℕ.suc n ]} (odd (step p))
    rewrite assert-evenness {+[1+ n ]} (even (suc-odd p)) =
      cong odd $ uniq-cert-odd (suc-even (suc-odd p)) (step p)
  assert-evenness { -[1+ ℕ.suc n ] } (even (pets p))
    rewrite assert-evenness { -[1+ n ] } (odd (neg-odd (suc-even p))) =
      cong even $ uniq-cert-even (pred-odd (neg-odd (suc-even p))) (pets p)
  assert-evenness { -[1+ ℕ.suc n ] } (odd (pets p))
    rewrite assert-evenness { -[1+ n ] } (even (neg-even (suc-odd p))) =
      cong odd $ uniq-cert-odd (pred-even (neg-even (suc-odd p))) (pets p)

  lemma-even : {z : ℤ} → (p : Even z) → even-or-odd z ≡ even p
  lemma-even p = assert-evenness (even p)

  lemma-odd : {z : ℤ} → (p : Odd z) → even-or-odd z ≡ odd p
  lemma-odd p = assert-evenness (odd p)

  even? : ℤ → Bool
  even? z with even-or-odd z
  ... | even _ = true
  ... | odd  _ = false

  odd? : ℤ → Bool
  odd? z = not (even? z)

