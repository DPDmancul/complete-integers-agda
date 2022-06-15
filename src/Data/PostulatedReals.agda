
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
  open ≡-Reasoning
  open import Data.N
  open ℕ
  import Data.Nat.Properties as ℕp
  open import Data.Int hiding (∣_∣ ; suc)
  open ℤ
  import Data.Int.Properties as ℤp
  open import Data.Empty
  open import Data.Sum
  open import Utils

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
      +-assoc : (x y z : ℝ) → (x + y) + z ≡ x + (y + z)

      *-zeroˡ : (x : ℝ) → additive-zero · x ≡ additive-zero
      *-comm : (x y : ℝ) → x · y ≡ y · x
      *-assoc : (x y z : ℝ) → (x · y) · z ≡ x · (y · z)

    +-identityʳ : (x : ℝ) → x + additive-zero ≡ x
    +-identityʳ x rewrite +-comm x additive-zero = +-identityˡ x

    +-assoc-middle : (a b c d : ℝ) → (a + b) + (c + d) ≡ a + (b + c) + d
    +-assoc-middle = •-assoc-middle _+_ +-assoc

    +-comm-middle : (a b c d : ℝ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
    +-comm-middle = •-comm-middle _+_ +-comm +-assoc-middle

    *-identityʳ : (x : ℝ) → x · unit ≡ x
    *-identityʳ x rewrite *-comm x unit = *-identityˡ x

    *-assoc-middle : (a b c d : ℝ) → (a · b) · (c · d) ≡ a · (b · c) · d
    *-assoc-middle = •-assoc-middle _·_ *-assoc

    *-comm-middle : (a b c d : ℝ) → (a · b) · (c · d) ≡ (a · c) · (b · d)
    *-comm-middle = •-comm-middle _·_ *-comm *-assoc-middle

    postulate
      x/x : (x : ℝ) {_ : x ≡ 0ℝ → ⊥} → x / x ≡ unit
      /-mul : (a b c d : ℝ) → a / b · c / d ≡ (a · c) / (b · d)
      x/1 : (x : ℝ) → x / unit ≡ x

    /-simplˡ : (x y z : ℝ) {_ : x ≡ 0ℝ → ⊥} → (x · y) / (x · z) ≡ y / z
    /-simplˡ x y z {p} rewrite sym (/-mul x x y z) | x/x x {p} = *-identityˡ (y / z)

    /-coef : (x y z : ℝ) → x · y / z ≡ (x · y) / z
    /-coef x y z rewrite sym (x/1 x) | /-mul x 1ℝ y z | x/1 x | *-identityˡ z = refl

    /-coef-simplˡ : (x y z : ℝ) {_ : x ≡ 0ℝ → ⊥} → x · y / (x · z) ≡ y / z
    /-coef-simplˡ x y z {p} rewrite /-coef x y (x · z) = /-simplˡ x y z {p}

    private
      1/1/x-help : (x : ℝ) {_ : x ≡ 0ℝ → ⊥} → x · 1ℝ / x ≡ 1ℝ
      1/1/x-help x {p} rewrite /-coef x 1ℝ x | *-identityʳ x =  x/x x {p}

    1/1/x : (x : ℝ) {_ : x ≡ 0ℝ → ⊥} → unit / (unit / x) ≡ x
    1/1/x x {p} rewrite sym (*-identityˡ (1ℝ / (1ℝ / x)))
      | sym (x/x x {p}) | /-mul x x (x / x) ((x / x) / x) | x/x x {p}
      | 1/1/x-help x {p} | sym (/-coef x 1ℝ 1ℝ) | x/1 1ℝ = *-identityʳ x

    postulate
      ∣x∣² : (x : ℝ) → ∣ x ∣ ^ 2 ≡ x ^ 2

    ∣x∣∣x∣ : (x : ℝ) → ∣ x ∣ · ∣ x ∣ ≡ x ^ 2
    ∣x∣∣x∣ x = trans (cong (_·_ ∣ x ∣) (sym (*-identityʳ ∣ x ∣))) (∣x∣² x)

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

    mul-base-ℕ : (x y : ℝ) → (n : ℕ) → (x · y) ^ n ≡ x ^ n · y ^ n
    mul-base-ℕ x y 0       = sym (*-identityʳ 1ℝ)
    mul-base-ℕ x y (suc n) rewrite *-comm-middle x (x ^ n) y (y ^ n) =
      cong (_·_ (x · y)) (mul-base-ℕ x y n)

    mul-base : (x y : ℝ) → (z : ℤ) → (x · y) ^ z ≡ x ^ z · y ^ z
    mul-base x y (pos n)  = mul-base-ℕ x y n
    mul-base x y -[1+ n ] rewrite /-mul 1ℝ (x ^ suc n) 1ℝ (y ^ suc n)
      | *-identityˡ 1ℝ = cong (_/_ 1ℝ) (mul-base-ℕ x y (suc n))

    1^n : (n : ℕ) → 1ℝ ^ n ≡ 1ℝ
    1^n 0       = refl
    1^n (suc n) rewrite 1^n n = *-identityˡ 1ℝ

    double-exp-ℕ : (x : ℝ) → (n m : ℕ) → (x ^ n) ^ m ≡ x ^ (n · m)
    double-exp-ℕ x 0       m = 1^n m
    double-exp-ℕ x (suc n) m rewrite mul-base-ℕ x (x ^ n) m
      | double-exp-ℕ x n m = sym (sum-exp-ℕ x m (n · m))

    x^nm=x^mn : (x : ℝ) → (n m : ℕ) → (x ^ n) ^ m ≡ (x ^ m) ^ n
    x^nm=x^mn x n m rewrite double-exp-ℕ x n m | ℕp.*-comm n m =
      sym (double-exp-ℕ x m n)

    private
      double-exp-help : (x : ℝ) → (n m : ℕ) →
        1ℝ / ((x ^ n) ^ suc m) ≡ x ^ (pos n · -[1+ m ])
      double-exp-help x 0       m rewrite 1^n m | *-identityˡ 1ℝ = x/1 1ℝ
      double-exp-help x (suc n) m = cong (_/_ 1ℝ) (double-exp-ℕ x (suc n) (suc  m))

    postulate
      x·y≡0 : (x y : ℝ) → x · y ≡ 0ℝ → x ≡ 0ℝ ⊎ y ≡ 0ℝ

    x^n≢0 : (x : ℝ) {_ : x ≡ 0ℝ → ⊥} → (n : ℕ) → x ^ n ≡ 0ℝ → ⊥
    x^n≢0 _     0       q = 1≢0 q
    x^n≢0 x {p} (suc n) q  with x·y≡0 x (x ^ n) q
    ... | inj₁ x≡0   = p x≡0
    ... | inj₂ x^n≡0 with x^n≢0 x {p} n
    ... | s = s x^n≡0

    mutual
      [1/x]^n : (x : ℝ) {_ : x ≡ 0ℝ → ⊥} → (n : ℕ) → (1ℝ / x) ^ n ≡ 1ℝ / (x ^ n)
      [1/x]^n x {p} n = begin
        (1ℝ / x) ^ pos n ≡⟨ cong (λ x → (1ℝ / x) ^ n) (sym (*-identityʳ x)) ⟩
        (x ^ -[1+ 0 ]) ^ pos n ≡⟨ helper x n ⟩
        x ^ (-[1+ 0 ] · pos n) ≡⟨ cong (_^_ x) (ℤp.*-comm -[1+ 0 ] (pos n)) ⟩
        x ^ (pos n · -[1+ 0 ]) ≡⟨ sym (double-exp x {p} (pos n) -[1+ 0 ]) ⟩
        (x ^ n) ^ -[1+ 0 ]     ≡⟨ cong (_/_ 1ℝ) (*-identityʳ (x ^ n)) ⟩
        1ℝ / (x ^ n)           ∎
        where
        helper : (x : ℝ) → (n : ℕ) → (1ℝ / (x · 1ℝ)) ^ n ≡ x ^ (-[1+ 0 ] · pos n)
        helper x 0             = refl
        helper x (suc n) rewrite helper x n | ℕp.+-identityʳ n | *-identityʳ x
          with n
        ... | 0     rewrite *-identityʳ x | *-identityʳ (1ℝ / x) = refl
        ... | suc n rewrite /-mul 1ℝ x 1ℝ (x ^ suc n) | *-identityˡ 1ℝ = refl

      [x/y]^n : (x y : ℝ) {_ : y ≡ 0ℝ → ⊥} → (n : ℕ) → (x / y) ^ n ≡ (x ^ n) / (y ^ n)
      [x/y]^n x y {p} n rewrite sym (*-identityʳ x) | mul-base-ℕ x 1ℝ n | 1^n n
        | sym (/-coef (x ^ n) 1ℝ (y ^ n)) | sym ([1/x]^n y {p} n)
        | sym (mul-base-ℕ x (1ℝ / y) n) | /-coef x 1ℝ y = refl

      double-exp : (x : ℝ) {_ : x ≡ 0ℝ → ⊥} → (z w : ℤ) → (x ^ z) ^ w ≡ x ^ (z · w)
      double-exp x     (pos n)  (pos m)  rewrite ℤp.pos-mul n m =
        double-exp-ℕ x n m
      double-exp x     (pos n)  -[1+ m ] = double-exp-help x n m
      double-exp x {p} -[1+ n ] (pos m)
        rewrite [1/x]^n (x ^ suc n) {x^n≢0 x {p} (suc n)} m
        | x^nm=x^mn x (suc n) m | ℤp.*-comm -[1+ n ] (pos m) =
        double-exp-help x m n
      double-exp x {p} -[1+ n ] -[1+ m ]
        rewrite [1/x]^n (x ^ suc n) {x^n≢0 x {p} (suc n)} m
        | /-mul 1ℝ (x ^ suc n) 1ℝ ((x ^ suc n) ^ m) | *-identityˡ 1ℝ
        | double-exp-ℕ x (suc n) m | sym (sum-exp-ℕ x (suc n) (m + n · m))
        | 1/1/x (x ^ suc (n + (m + (n · m))))
        {x^n≢0 x {p} (suc (n + (m + (n · m))))} =
        cong (λ y → x ^ suc y) (helper n m)
        where
        helper : (n m : ℕ) → n + (m + n · m) ≡ m + (n · suc m)
        helper n m rewrite ℕp.*-comm n (suc m) | ℕp.*-comm m n = begin
          (n + (m + n · m)) ≡⟨ sym (ℕp.+-assoc n m (n · m)) ⟩
          ((n + m) + n · m) ≡⟨ cong (_+ n · m) (ℕp.+-comm n m) ⟩
          ((m + n) + n · m) ≡⟨ ℕp.+-assoc m n (n · m) ⟩
          (m + (n + n · m)) ∎
