
-- (c) Davide Peressoni 2022

-- {-# OPTIONS --safe --without-K #-}

-- To allow generating HTML output even if not complete
{-# OPTIONS --allow-unsolved-metas --without-K #-}

------------------
-- Real numbers --
------------------

-- Constructive real numbers according to Bishop

module Data.R where
  open import Data.N as ℕ using (ℕ ; suc ; s≤s ; z≤n)
  import Data.Nat.Properties as ℕp
  open import Data.Nat.Coprimality using (1-coprimeTo)
  open import Data.Int as ℤ using (ℤ ; 1ℤ)
  open import Data.Q
  open import Data.Rational.Properties
  open import Data.Product
  open import Relation.Binary.PropositionalEquality

  open import Ops

  Seq = ℕ → ℚ

  record ℝ : Set where
    field
      seq : Seq
      reg : (n m : ℕ) → ∣ seq (suc n) - seq (suc m) ∣ ≤ suc n ⁻¹ + suc m ⁻¹

  reg : (x : ℝ) (n : ℕ) {p : n ≢0} (m : ℕ) {q : m ≢0} →
    ∣ ℝ.seq x n - ℝ.seq x m ∣ ≤ n ⁻¹⟨ p ⟩ + m ⁻¹⟨ q ⟩
  reg x (suc n) (suc m) = ℝ.reg x n m

  fromℚ : ℚ → ℝ
  ℝ.seq (fromℚ q) _ = q
  ℝ.reg (fromℚ q) n m = begin
    ∣ q - q ∣ ≡⟨ cong ∣_∣ (+-inverseʳ q) ⟩
    0ℚ        ≤⟨ +-mono-≤ {0ℚ} {suc n ⁻¹} {0ℚ} {suc m ⁻¹}
                  (nonNegative⁻¹ (normalize-nonNeg 1 (suc n)))
                  (nonNegative⁻¹ (normalize-nonNeg 1 (suc m))) ⟩
    suc n ⁻¹ + suc m ⁻¹ ∎
    where open ≤-Reasoning

  0ℝ : ℝ
  0ℝ = fromℚ 0ℚ

  1ℝ : ℝ
  1ℝ = fromℚ 1ℚ

  ---------------------
  -- Canonical bound --
  ---------------------

  bound : Seq → ℕ
  bound x = suc (suc ℤ.∣ (ceil ∣ x 1 ∣) ∣)

  bound-is-max : (x : ℝ) → (n : ℕ) → ∣ (ℝ.seq x) (suc n) ∣ ≤ ℕtoℚ (bound (ℝ.seq x))
  bound-is-max x n = let
      seq = ℝ.seq x
      x1 = seq 1
      xn = seq (suc n)
    in ≤-trans (help₁ {xn} {x1} (begin
    ∣ xn - x1 ∣   ≤⟨ ℝ.reg x n 0 ⟩
    suc n ⁻¹ + 1ℚ ≤⟨ +-monoˡ-≤ 1ℚ (≥⁻¹ (s≤s (z≤n {n}))) ⟩
    2ℚ ∎)) (help₂ x1)
    where
    open ≤-Reasoning
    help₁ : {a b c : ℚ} → ∣ a - b ∣ ≤ c → ∣ a ∣ ≤ ∣ b ∣ + c
    help₁ {a} {b} {c} p = begin
      ∣ a ∣                 ≡⟨ lemma-+ ∣ a ∣ ∣ b ∣ ⟩
      ∣ a ∣ - ∣ b ∣ + ∣ b ∣ ≤⟨ +-monoˡ-≤ ∣ b ∣ (∣a∣-∣b∣≤∣a-b∣ a b) ⟩
      ∣ a - b ∣ + ∣ b ∣     ≤⟨ +-monoˡ-≤ ∣ b ∣ p ⟩
      c + ∣ b ∣             ≡⟨ +-comm c ∣ b ∣ ⟩
      ∣ b ∣ + c             ∎
    help₂ : (x : ℚ) → ∣ x ∣ + 2ℚ ≤ ℕtoℚ (suc (suc ℤ.∣ (ceil ∣ x ∣) ∣))
    help₂ = {!   !}

  bound-is-max-nonZero : (x : ℝ) → (n : ℕ) {_ : n ≢0} →
    ∣ (ℝ.seq x) n ∣ ≤ ℕtoℚ (bound (ℝ.seq x))
  bound-is-max-nonZero x (suc n) = bound-is-max x n

  --------------
  -- Equality --
  --------------


  ----------------
  -- Operations --
  ----------------

  instance
    Sumℝ : Sum ℝ
    ℝ.seq (_+_ ⦃ Sumℝ ⦄ x y) n = ℝ.seq x (2 · n) + ℝ.seq y (2 · n)
    ℝ.reg (_+_ ⦃ Sumℝ ⦄ x y) n m = let
      x2n = ℝ.seq x (2 · suc n)
      y2n = ℝ.seq y (2 · suc n)
      x2m = ℝ.seq x (2 · suc m)
      y2m = ℝ.seq y (2 · suc m)
      in begin
      ∣ (x2n + y2n) - (x2m + y2m) ∣
        ≡⟨ cong (λ z → ∣ (x2n + y2n) + z ∣) (neg-distrib-+ x2m y2m) ⟩
      ∣ (x2n + y2n) + (- x2m - y2m) ∣
        ≡⟨ cong ∣_∣ (+-assoc x2n y2n (- x2m - y2m)) ⟩
      ∣ x2n + (y2n + (- x2m - y2m)) ∣
        ≡⟨ cong (λ z → ∣ x2n + z ∣) (sym (+-assoc y2n (- x2m) (- y2m))) ⟩
      ∣ x2n + (y2n - x2m - y2m) ∣
        ≡⟨ cong (λ z → ∣ x2n + (z - y2m) ∣) (+-comm y2n (- x2m)) ⟩
      ∣ x2n + (- x2m + y2n - y2m) ∣
        ≡⟨ cong (λ z → ∣ x2n + z ∣) (+-assoc (- x2m) y2n (- y2m)) ⟩
      ∣ x2n + (- x2m + (y2n - y2m)) ∣
        ≡⟨ cong ∣_∣ (sym (+-assoc x2n (- x2m) (y2n - y2m))) ⟩
      ∣ (x2n - x2m) + (y2n - y2m) ∣ ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (x2n - x2m) (y2n - y2m) ⟩
      ∣ x2n - x2m ∣ + ∣ y2n - y2m ∣
        ≤⟨ +-mono-≤ (reg x (2 · suc n) (2 · suc m))
                    (reg y (2 · suc n) (2 · suc m)) ⟩
      ((2 · suc n)⁻¹ + (2 · suc m)⁻¹) +
      ((2 · suc n)⁻¹ + (2 · suc m)⁻¹)
        ≡⟨ +-comm-middle ((2 · suc n)⁻¹) ((2 · suc m)⁻¹)
                         ((2 · suc n)⁻¹) ((2 · suc m)⁻¹) ⟩
      ((2 · suc n)⁻¹ + (2 · suc n)⁻¹) + ((2 · suc m)⁻¹ + (2 · suc m)⁻¹)
        ≡⟨ cong₂ _+_ (helper n) (helper m) ⟩
      suc n ⁻¹ + suc m ⁻¹ ∎
      where
      helper : (n : ℕ) → (2 · suc n)⁻¹ + (2 · suc n)⁻¹ ≡ (suc n)⁻¹
      helper n = begin
        (2 · suc n)⁻¹ + (2 · suc n)⁻¹ ≡⟨ cong (λ x → x + x) (help-helper n) ⟩
        ½ · (suc n)⁻¹ + ½ · (suc n)⁻¹ ≡⟨ sym (*-distribʳ-+ ((suc n)⁻¹) ½ ½) ⟩
        1ℚ · (suc n)⁻¹                ≡⟨ *-identityˡ ((suc n)⁻¹) ⟩
        (suc n)⁻¹                     ∎
        where
        open ≡-Reasoning
        help-helper : (n : ℕ) → (2 · suc n)⁻¹ ≡ ½ · (suc n)⁻¹
        help-helper n rewrite normalize-coprime (1-coprimeTo (2 · suc n)) | ⁻¹≡ n =
          sym (normalize-coprime (1-coprimeTo (suc (n + suc (n + 0)))))
      open ≤-Reasoning

    additive-zero ⦃ Sumℝ ⦄ = 0ℝ
    lemma-sum-zero ⦃ Sumℝ ⦄ {x} = {!   !}

  instance
    Mulℝ : Mul ℝ
    ℝ.seq (_·_ ⦃ Mulℝ ⦄ x y) n = let k = bound (ℝ.seq x) ℕ.⊔ bound (ℝ.seq y)
      in ℝ.seq x (2 · k · n) · ℝ.seq y (2 · k · n)
    ℝ.reg (_·_ ⦃ Mulℝ ⦄ x y) n m = let
      kx = bound (ℝ.seq x)
      ky = bound (ℝ.seq y)
      k = kx ℕ.⊔ ky
      kℚ = ℕtoℚ k
      2k = 2 · k
      xn = ℝ.seq x (2k · suc n)
      yn = ℝ.seq y (2k · suc n)
      xm = ℝ.seq x (2k · suc m)
      ym = ℝ.seq y (2k · suc m)
      ∣xm∣≤k : ∣ xm ∣ ≤ kℚ
      ∣xm∣≤k = ≤-trans (bound-is-max-nonZero x (2k · suc m))
                       (ℕtoℚ-trans-≤ (ℕp.m≤m⊔n kx ky))
      ∣yn∣≤k : ∣ yn ∣ ≤ kℚ
      ∣yn∣≤k = ≤-trans (bound-is-max-nonZero y (2k · suc n))
                       (ℕtoℚ-trans-≤ (ℕp.m≤n⊔m kx ky))
      in begin
      ∣ xn · yn - xm · ym ∣ ≡⟨ cong ∣_∣ (sym (helper₁ xn xm yn ym)) ⟩
      ∣ (xn - xm) · yn + xm · (yn - ym) ∣
        ≡⟨ cong (λ z → ∣ z + xm · (yn - ym) ∣) (*-comm (xn - xm) yn) ⟩
      ∣ yn · (xn - xm) + xm · (yn - ym) ∣
        ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (yn · (xn - xm)) (xm · (yn - ym)) ⟩
      ∣ yn · (xn - xm) ∣ + ∣ xm · (yn - ym) ∣
        ≡⟨ cong₂ _+_ (∣p*q∣≡∣p∣*∣q∣ yn (xn - xm))
                     (∣p*q∣≡∣p∣*∣q∣ xm (yn - ym)) ⟩
      ∣ yn ∣ · ∣ xn - xm ∣ + ∣ xm ∣ · ∣ yn - ym ∣
        ≤⟨ helper₂ {∣ yn ∣} {∣ xm ∣} (reg x (2k · suc n) (2k · suc m))
                                     (reg y (2k · suc n) (2k · suc m)) ⟩
      ∣ yn ∣ · ((2k · suc n)⁻¹ + (2k · suc m)⁻¹) +
      ∣ xm ∣ · ((2k · suc n)⁻¹ + (2k · suc m)⁻¹)
        ≤⟨ +-mono-≤
          (*-monoʳ-≤-nonNeg ((2k · suc n)⁻¹ + (2k · suc m)⁻¹) {!   !} ∣yn∣≤k)
          (*-monoʳ-≤-nonNeg ((2k · suc n)⁻¹ + (2k · suc m)⁻¹) {!   !} ∣xm∣≤k) ⟩
      kℚ · ((2k · suc n)⁻¹ + (2k · suc m)⁻¹) +
      kℚ · ((2k · suc n)⁻¹ + (2k · suc m)⁻¹)
        ≡⟨ {!   !} ⟩
      kℚ · (((2k · suc n)⁻¹ + (2k · suc m)⁻¹) + ((2k · suc n)⁻¹ + (2k · suc m)⁻¹))
        ≡⟨ {! !} ⟩
      kℚ · ((2k · suc n)⁻¹ + (2k · suc n)⁻¹ + (2k · suc m)⁻¹ + (2k · suc m)⁻¹)
        ≡⟨ {!   !} ⟩
      kℚ · ((k · suc n)⁻¹ + (k · suc m)⁻¹)
        ≡⟨ {!   !} ⟩
      kℚ · (k · suc n)⁻¹ + kℚ · (k · suc m)⁻¹
        ≡⟨ {!   !} ⟩
        {!   !} ≡⟨ {!   !} ⟩
      suc n ⁻¹ + suc m ⁻¹ ∎
      where
      helper₁ : (a b c d : ℚ) → (a - b) · c + b · (c - d) ≡ a · c - b · d
      helper₁ a b c d = begin
        (a - b) · c + b · (c - d)
          ≡⟨ cong₂ _+_ (*-distribʳ-+ c a (- b)) (*-distribˡ-+ b c (- d)) ⟩
        (a · c + (- b) · c) + (b · c + b · (- d))
          ≡⟨ cong₂ (λ w z → (a · c + w) + (b · c + z))
            (sym (neg-distribˡ-* b c)) (sym (neg-distribʳ-* b d)) ⟩
        (a · c - b · c) + (b · c - b · d)
          ≡⟨ sym (+-assoc (a · c  - b · c) (b · c) (- (b · d))) ⟩
        a · c - b · c + b · c - b · d
          ≡⟨ cong (_- b · d) (+-assoc (a · c) (- (b · c)) (b · c)) ⟩
        a · c + (- (b · c) + b · c) - b · d
          ≡⟨ cong (λ z → a · c + z - b · d) (+-inverseˡ (b · c)) ⟩
        a · c + 0ℚ - b · d
          ≡⟨ cong (_- b · d) (+-identityʳ (a · c)) ⟩
        a · c - b · d ∎
        where open ≡-Reasoning
      open ≤-Reasoning
      helper₂ : {a c b₁ b₂ d₁ d₂ : ℚ} →
        {a>0 : NonNegative a} → {c>0 : NonNegative c} →
        b₁ ≤ b₂ → d₁ ≤ d₂ → a · b₁ + c · d₁ ≤ a · b₂ + c · d₂
      helper₂ {a} {c} {a>0 = a>0} {c>0 = c>0} p q = +-mono-≤
        (*-monoˡ-≤-nonNeg a a>0 p) (*-monoˡ-≤-nonNeg c c>0 q)

    unit ⦃ Mulℝ ⦄ = 1ℝ
    lemma-unit ⦃ Mulℝ ⦄ {x} = {!   !}


