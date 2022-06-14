
-- (c) Davide Peressoni 2022

{-# OPTIONS --without-K #-}

-----------------------------
-- Postulated real numbers --
-----------------------------

-- I tried defining real numbers (R.agda) but it was taking too much time and
-- also loading the file and giving goals a value was consuming too much RAM.
-- So here I postulate the real numbers and their properties I need in my work.

module Data.PostulatedReals where

  open import Relation.Binary.PropositionalEquality
  open import Data.N
  open ℕ
  open import Data.Int hiding (∣_∣ ; suc)
  open ℤ
  open import Data.Empty

  postulate
    ℝ : Set
    0ℝ : ℝ
    1ℝ : ℝ

    addℝ : ℝ → ℝ → ℝ
    negℝ : ℝ → ℝ
    mulℝ : ℝ → ℝ → ℝ
    _/_ : ℝ → ℝ → ℝ
    ∣_∣ : ℝ → ℝ

    1≢0 : 1ℝ ≡ 0ℝ → ⊥

  open import Ops

  private postulate
    lemma-+-identityˡ : (x : ℝ) → addℝ 0ℝ x ≡ x
    lemma-*-identityˡ : (x : ℝ) → mulℝ 1ℝ x ≡ x

  instance
    Sumℝ : Sum ℝ
    _+_ ⦃ Sumℝ ⦄ = addℝ
    additive-zero ⦃ Sumℝ ⦄ = 0ℝ
    lemma-sum-zero ⦃ Sumℝ ⦄ {x} = lemma-+-identityˡ x

    Subℝ : Sub ℝ
    -_ ⦃ Subℝ ⦄ = negℝ

    Mulℝ : Mul ℝ
    _·_ ⦃ Mulℝ ⦄ = mulℝ
    unit ⦃ Mulℝ ⦄ = 1ℝ
    lemma-unit ⦃ Mulℝ ⦄ {x} = lemma-*-identityˡ x

    IntPowℝ : Pow ℝ ℤ {ℝ}
    _^_ ⦃ IntPowℝ ⦄ b (ℤ.pos n) = b ^ n
    _^_ ⦃ IntPowℝ ⦄ b -[1+ n ]  = unit / (b ^ ℕ.suc n)


  ----------------
  -- Properties --
  ----------------

  module Properties where

    +-identityˡ = lemma-+-identityˡ
    *-identityˡ = lemma-*-identityˡ

    postulate
      +-comm : (x y : ℝ) → x + y ≡ y + x

      *-zeroˡ : (x : ℝ) → additive-zero · x ≡ additive-zero
      *-comm : (x y : ℝ) → x · y ≡ y · x
      *-assoc : (x y z : ℝ) → (x · y) · z ≡ x · (y · z)

    +-identityʳ : (x : ℝ) → x + additive-zero ≡ x
    +-identityʳ x rewrite +-comm x additive-zero = +-identityˡ x

    *-identityʳ : (x : ℝ) → x · unit ≡ x
    *-identityʳ x rewrite *-comm x unit = *-identityˡ x

    postulate
      /-simplˡ : (x y z : ℝ) {_ : x ≡ 0ℝ → ⊥} → (x · y) / (x · z) ≡ y / z
      x/x : (x : ℝ) {_ : x ≡ 0ℝ → ⊥} → x / x ≡ unit
      /-mul : (a b c d : ℝ) → a / b · c / d ≡ (a · c) / (b · d)
      x/1 : (x : ℝ) → x / unit ≡ x

    /-coef : (x y z : ℝ) → x · y / z ≡ (x · y) / z
    /-coef x y z rewrite sym (x/1 x) | /-mul x 1ℝ y z | x/1 x | *-identityˡ z = refl

    /-coef-simplˡ : (x y z : ℝ) {_ : x ≡ 0ℝ → ⊥} → x · y / (x · z) ≡ y / z
    /-coef-simplˡ x y z {p} rewrite /-coef x y (x · z) = /-simplˡ x y z {p}

    postulate
      ∣x∣² : (x : ℝ) → ∣ x ∣ ^ 2 ≡ x ^ 2


    --------------------
    -- Exponent rules --
    --------------------

    import Data.Integer.Properties as ℤp

    sum-exp-ℕ : (x : ℝ) → (n m : ℕ) → x ^ (n + m) ≡ x ^ n · x ^ m
    sum-exp-ℕ x zero      m = sym (*-identityˡ (x ^ m))
    sum-exp-ℕ x (ℕ.suc n) m rewrite *-assoc x (x ^ n) (x ^ m) =
      cong (_·_ x) (sum-exp-ℕ x n m)

    private
      sum-exp-help : (x : ℝ) {_ : x ≡ 0ℝ → ⊥} → (n m : ℕ) →
        x ^ (pos n  + -[1+ m ]) ≡ x ^ pos n · x ^ -[1+ m ]
      sum-exp-help x     0       m = sym (*-identityˡ  (1ℝ / (x · x ^ m)))
      sum-exp-help x {p} (suc n) 0 rewrite *-comm x (x ^ n)
        | *-assoc (x ^ n) x (1ℝ / (x · 1ℝ)) | /-coef-simplˡ x 1ℝ 1ℝ {p}
        | x/x 1ℝ {1≢0} = sym (*-identityʳ (x ^ n))
      sum-exp-help x {p} (suc n) (suc m) rewrite ℤp.[1+m]⊖[1+n]≡m⊖n n (suc m)
        | *-comm x (x ^ n) | *-assoc (x ^ n) x (1ℝ / (x · (x · x ^ m)))
        | /-coef-simplˡ x 1ℝ (x · x ^ m) {p} = sum-exp-help x {p} n m

    sum-exp : (x : ℝ) {_ : x ≡ 0ℝ → ⊥} → (z w : ℤ) → x ^ (z + w) ≡ x ^ z · x ^ w
    sum-exp x     (pos n)  (pos m)  = sum-exp-ℕ x n m
    sum-exp x {p} (pos n)  -[1+ m ] = sum-exp-help x {p} n m
    sum-exp x {p} -[1+ n ] (pos m)  rewrite *-comm (1ℝ / (x · x ^ n)) (x ^ m) =
      sum-exp-help x {p} m n
    sum-exp x {p} -[1+ n ] -[1+ m ] rewrite /-mul 1ℝ (x · x ^ n) 1ℝ (x · x ^ m)
      | *-identityˡ 1ℝ | *-assoc x (x ^ n) (x · x ^ m)
      | sym (*-assoc (x ^ n) x (x ^ m)) | *-comm (x ^ n) x
      | *-assoc x (x ^ n) (x ^ m) =
      cong (λ y →  1ℝ / (x · (x · y))) (sum-exp-ℕ x n m)

    -- double-exp : (x : ℝ) → (z w : ℤ) → (x ^ z) ^ w ≡ x ^ (z · w)
    -- double-exp x z w = {!   !}

    -- mul-base : (x y : ℝ) → (z : ℤ) → (x · y) ^ z ≡ x ^ z · y ^ z
    -- mul-base x y z = {!   !}

