
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

------------------
-- Real numbers --
------------------

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

  bound : Seq → ℕ
  bound x = ℤ.∣_∣ (ceil ∣ x 1 ∣) + 2

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
      ∣ a ∣                 ≡⟨ {!   !} ⟩
      ∣ a ∣ - ∣ b ∣ + ∣ b ∣ ≤⟨ {!   !} ⟩
      ∣ a - b ∣ + ∣ b ∣     ≤⟨ {!   !} ⟩
      c + ∣ b ∣             ≡⟨ {!   !} ⟩
      ∣ b ∣ + c             ∎
    help₂ : (x : ℚ) → ∣ x ∣ + 2ℚ ≤ ℕtoℚ (ℤ.∣_∣ (ceil ∣ x ∣) + 2)
    help₂ = {!   !}

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
        ≤⟨ +-mono-≤ (ℝ.reg x (ℕ.pred (2 · suc n)) (ℕ.pred (2 · suc m)))
                    (ℝ.reg y (ℕ.pred (2 · suc n)) (ℕ.pred (2 · suc m))) ⟩
      ((2 · suc n)⁻¹ + (2 · suc m)⁻¹) +
      ((2 · suc n)⁻¹ + (2 · suc m)⁻¹)
        ≡⟨ +-comm-middle ((2 · suc n)⁻¹) ((2 · suc m)⁻¹)
                         ((2 · suc n)⁻¹) ((2 · suc m)⁻¹) ⟩
      ((2 · suc n)⁻¹ + (2 · suc n)⁻¹) + ((2 · suc m)⁻¹ + (2 · suc m)⁻¹)
        ≡⟨ cong₂ _+_ (helper n) (helper m) ⟩
      suc n ⁻¹ + suc m ⁻¹ ∎
      where
      -- help₁ : (n m : ℕ) → (suc (suc (2 · n)))⁻¹ + (suc (suc (2 · m)))⁻¹ ≡
      --   (2 · (suc n))⁻¹ + (2 · (suc m))⁻¹
      -- help₁ n m = cong₂ _+_ (helper n) (helper m)
      --   where
      --   helper : (n : ℕ) → (suc (suc (2 · n)))⁻¹ ≡ (2 · suc n)⁻¹
      --   helper n = ⁻¹-trans (cong suc (sym (ℕp.+-suc n (n + 0))))
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
      k = bound (ℝ.seq x) ℕ.⊔ bound (ℝ.seq y)
      xn = ℝ.seq x (2 · k · suc n)
      yn = ℝ.seq y (2 · k · suc n)
      xm = ℝ.seq x (2 · k · suc m)
      ym = ℝ.seq y (2 · k · suc m)
      in begin
      ∣ xn · yn - xm · ym ∣ ≡⟨ cong ∣_∣ (sym (helper₁ xn xm yn ym)) ⟩
      ∣ (xn - xm) · yn + xm · (yn - ym) ∣
        ≡⟨ cong (λ z → ∣ z + xm · (yn - ym) ∣) (*-comm (xn - xm) yn) ⟩
      ∣ yn · (xn - xm) + xm · (yn - ym) ∣
        ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (yn · (xn - xm)) (xm · (yn - ym)) ⟩
      ∣ yn · (xn - xm) ∣ + ∣ xm · (yn - ym) ∣
        ≡⟨ cong₂ _+_ (∣p*q∣≡∣p∣*∣q∣ yn (xn - xm))
                     (∣p*q∣≡∣p∣*∣q∣ xm (yn - ym)) ⟩
      ∣ yn ∣ · ∣ xn - xm ∣ + ∣ xm ∣ · ∣ yn - ym ∣ ≤⟨ ? ⟩
        -- ≤⟨ +-mono-≤ (helper₂ yn xn xm (∣yn∣≤max n)
        --   (proj₂ (ℝ.reg x ε/2max>0) (ℕp.<-transʳ (ℕp.m≤m⊔n Nx Ny) q)
        --                             (ℕp.<-transʳ (ℕp.m≤m⊔n Nx Ny) r)))
        --                (helper₂ xm yn ym (∣xn∣≤max m)
        --   (proj₂ (ℝ.reg y ε/2max>0) (ℕp.<-transʳ (ℕp.m≤n⊔m Nx Ny) q)
        --                             (ℕp.<-transʳ (ℕp.m≤n⊔m Nx Ny) r))) ⟩
      -- ½ · ε + ½ · ε ≡⟨ sym (*-distribʳ-+ ε ½ ½) ⟩
      -- 1ℚ · ε        ≡⟨ *-identityˡ ε ⟩
      ? ≤⟨ ? ⟩
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
      x≤y⇒x<1+y : {x y : ℚ} → x ≤ y → x < 1ℚ + y
      x≤y⇒x<1+y {x} p = <-respˡ-≡ (+-identityˡ x)
        (+-mono-<-≤ (*<* {0ℚ} {1ℚ} (ℤ.+<+ (s≤s z≤n))) p)
      x≤y⇒x≤1+y : {x y : ℚ} → x ≤ y → x ≤ 1ℚ + y
      x≤y⇒x≤1+y p = <⇒≤ (x≤y⇒x<1+y p)
      -- ∣xn∣≤max : (n : ℕ) → ∣ ℝ.seq x n ∣ ≤ max
      -- ∣xn∣≤max n = x≤y⇒x≤1+y (≤-trans ((proj₂ argmax-x) n) (p≤p⊔q max-x max-y))
      -- ∣yn∣≤max : (n : ℕ) → ∣ ℝ.seq y n ∣ ≤ max
      -- ∣yn∣≤max n = x≤y⇒x≤1+y (≤-trans ((proj₂ argmax-y) n) (p≤q⊔p max-x max-y))
      -- max>0 : max > 0ℚ
      -- max>0 = x≤y⇒x<1+y (≤-trans (0≤∣p∣ max-x-signed) (p≤p⊔q max-x max-y))
      -- helper₂ : (a b c : ℚ) → ∣ a ∣ ≤ max → ∣ b - c ∣ ≤ ε/2max →
      --   ∣ a ∣ · ∣ b - c ∣ ≤ ½ · ε
      -- helper₂ a b c p q = begin
      --   ∣ a ∣ · ∣ b - c ∣ ≡⟨ *-comm ∣ a ∣ ∣ b - c ∣ ⟩
      --   ∣ b - c ∣ · ∣ a ∣
      --     ≤⟨ *-monoˡ-≤-nonNeg ∣ b - c ∣ (nonNegative (0≤∣p∣ a)) p ⟩
      --   ∣ b - c ∣ · max
      --     ≤⟨ {!   !} ⟩
      --     -- ≤⟨ *-monoʳ-≤-nonNeg max (nonNegative (0≤∣p∣ (b - c))) q ⟩


    unit ⦃ Mulℝ ⦄ = 1ℝ
    lemma-unit ⦃ Mulℝ ⦄ {x} = {!   !}


