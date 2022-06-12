
-- (c) Davide Peressoni 2022

{-# OPTIONS --without-K #-}

------------------
-- Real numbers --
------------------

module Data.R where
  open import Data.N as ℕ hiding (_≤_ ; _<_ ; _>_ ; ∣_-_∣ ; _≟_ ; _⊔_)
  open import Data.Q
  import Data.Int as ℤ
  import Data.Nat.Properties as ℕp
  open import Data.Rational.Properties
  open import Data.Product
  open import Relation.Binary.PropositionalEquality
  open import Max 0 ≤-<-connex

  open import Ops

  record ℝ : Set where
    field
      seq : ℕ → ℚ
      reg : ∀ {ε : ℚ} → ε > 0ℚ → ∃[ N ] ∀ {n m : ℕ} → n ℕ.> N → m ℕ.> N →
        ∣ seq n - seq m ∣ ≤ ε

  fromℚ : ℚ → ℝ
  ℝ.seq (fromℚ q) _ = q
  ℝ.reg (fromℚ q) {ε} p = 0 , λ _ _ → begin
    ∣ q - q ∣ ≡⟨ cong ∣_∣ (+-inverseʳ q) ⟩
    0ℚ        ≤⟨ <⇒≤ p ⟩
    ε         ∎
    where open ≤-Reasoning

  0ℝ : ℝ
  0ℝ = fromℚ 0ℚ

  1ℝ : ℝ
  1ℝ = fromℚ 1ℚ

  private
    ε>0⇒ε/2>0 : {ε : ℚ} → ε > 0ℚ → ½ · ε > 0ℚ
    ε>0⇒ε/2>0 {ε} p = <-respˡ-≡ (*-zeroˡ ε)
      (*-monoˡ-<-pos ε (positive p) (*<* {0ℚ} {½} (ℤ.+<+ (s≤s z≤n))))

  instance
    Sumℝ : Sum ℝ
    ℝ.seq (_+_ ⦃ Sumℝ ⦄ x y) n = ℝ.seq x n + ℝ.seq y n
    ℝ.reg (_+_ ⦃ Sumℝ ⦄ x y) {ε} p = N , λ {n} {m} q r →  let
      xn = ℝ.seq x n
      yn = ℝ.seq y n
      xm = ℝ.seq x m
      ym = ℝ.seq y m
      in begin
      ∣ (xn + yn) - (xm + ym) ∣
        ≡⟨ cong (λ z → ∣ (xn + yn) + z ∣) (neg-distrib-+ xm ym) ⟩
      ∣ (xn + yn) + (- xm - ym) ∣
        ≡⟨ cong ∣_∣ (+-assoc xn yn (- xm - ym)) ⟩
      ∣ xn + (yn + (- xm - ym)) ∣
        ≡⟨ cong (λ z → ∣ xn + z ∣) (sym (+-assoc yn (- xm) (- ym))) ⟩
      ∣ xn + (yn - xm - ym) ∣
        ≡⟨ cong (λ z → ∣ xn + (z - ym) ∣) (+-comm yn (- xm)) ⟩
      ∣ xn + (- xm + yn - ym) ∣
        ≡⟨ cong (λ z → ∣ xn + z ∣) (+-assoc (- xm) yn (- ym)) ⟩
      ∣ xn + (- xm + (yn - ym)) ∣
        ≡⟨ cong ∣_∣ (sym (+-assoc xn (- xm) (yn - ym))) ⟩
      ∣ (xn - xm) + (yn - ym) ∣ ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (xn - xm) (yn - ym) ⟩
      ∣ xn - xm ∣ + ∣ yn - ym ∣
        ≤⟨ +-mono-≤ (proj₂ (ℝ.reg x ε/2>0) (ℕp.<-transʳ (ℕp.m≤m⊔n Nx Ny) q)
                                              (ℕp.<-transʳ (ℕp.m≤m⊔n Nx Ny) r))
                       (proj₂ (ℝ.reg y ε/2>0) (ℕp.<-transʳ (ℕp.n≤m⊔n Nx Ny) q)
                                              (ℕp.<-transʳ (ℕp.n≤m⊔n Nx Ny) r)) ⟩
      ½ · ε + ½ · ε ≡⟨ sym (*-distribʳ-+ ε ½ ½) ⟩
      1ℚ · ε        ≡⟨ *-identityˡ ε ⟩
      ε             ∎
      where
      open ≤-Reasoning
      ε/2>0 = ε>0⇒ε/2>0 p
      N Nx Ny : ℕ
      Nx = proj₁ (ℝ.reg x ε/2>0)
      Ny = proj₁ (ℝ.reg y ε/2>0)
      N  = Nx ℕ.⊔ Ny

    additive-zero ⦃ Sumℝ ⦄ = 0ℝ
    lemma-sum-zero ⦃ Sumℝ ⦄ {x} = {!   !}

  instance
    Mulℝ : Mul ℝ
    ℝ.seq (_·_ ⦃ Mulℝ ⦄ x y) n = ℝ.seq x n · ℝ.seq y n
    ℝ.reg (_·_ ⦃ Mulℝ ⦄ x y) {ε} p = N , λ {n} {m} q r →  let
      xn = ℝ.seq x n
      yn = ℝ.seq y n
      xm = ℝ.seq x m
      ym = ℝ.seq y m
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
        ≤⟨ +-mono-≤ (helper₂ yn xn xm (∣yn∣≤max n)
          (proj₂ (ℝ.reg x ε/2max>0) (ℕp.<-transʳ (ℕp.m≤m⊔n Nx Ny) q)
                                    (ℕp.<-transʳ (ℕp.m≤m⊔n Nx Ny) r)))
                       (helper₂ xm yn ym (∣xn∣≤max m)
          (proj₂ (ℝ.reg y ε/2max>0) (ℕp.<-transʳ (ℕp.n≤m⊔n Nx Ny) q)
                                    (ℕp.<-transʳ (ℕp.n≤m⊔n Nx Ny) r))) ⟩
      ½ · ε + ½ · ε ≡⟨ sym (*-distribʳ-+ ε ½ ½) ⟩
      1ℚ · ε        ≡⟨ *-identityˡ ε ⟩
      ε             ∎
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
      argmax-x : Σ[ n ∈ ℕ ] ((m : ℕ) → ∣ ℝ.seq x m ∣ ≤ ∣ ℝ.seq x n ∣)
      argmax-x = maximum (λ n → ∣ ℝ.seq x n ∣)
      max-x-signed : ℚ
      max-x-signed = ℝ.seq x (proj₁ argmax-x)
      max-x : ℚ
      max-x = ∣ max-x-signed ∣
      argmax-y : Σ[ n ∈ ℕ ] ((m : ℕ) → ∣ ℝ.seq y m ∣ ≤ ∣ ℝ.seq y n ∣)
      argmax-y = maximum (λ n → ∣ ℝ.seq y n ∣)
      max-y-signed : ℚ
      max-y-signed = ∣ ℝ.seq y (proj₁ argmax-y) ∣
      max-y : ℚ
      max-y = ∣ max-y-signed ∣
      max : ℚ
      max = 1ℚ + (max-x ⊔ max-y)
      x≤y⇒x<1+y : {x y : ℚ} → x ≤ y → x < 1ℚ + y
      x≤y⇒x<1+y {x} p = <-respˡ-≡ (+-identityˡ x)
        (+-mono-<-≤ (*<* {0ℚ} {1ℚ} (ℤ.+<+ (s≤s z≤n))) p)
      x≤y⇒x≤1+y : {x y : ℚ} → x ≤ y → x ≤ 1ℚ + y
      x≤y⇒x≤1+y p = <⇒≤ (x≤y⇒x<1+y p)
      ∣xn∣≤max : (n : ℕ) → ∣ ℝ.seq x n ∣ ≤ max
      ∣xn∣≤max n = x≤y⇒x≤1+y (≤-trans ((proj₂ argmax-x) n) (p≤p⊔q max-x max-y))
      ∣yn∣≤max : (n : ℕ) → ∣ ℝ.seq y n ∣ ≤ max
      ∣yn∣≤max n = x≤y⇒x≤1+y (≤-trans ((proj₂ argmax-y) n) (p≤q⊔p max-x max-y))
      max>0 : max > 0ℚ
      max>0 = x≤y⇒x<1+y (≤-trans (0≤∣p∣ max-x-signed) (p≤p⊔q max-x max-y))
      ε/2max = ½ · ε ÷ max
      ε/2max>0 : ε/2max > 0ℚ
      ε/2max>0 = <-respˡ-≡ (*-zeroˡ (1/ max))
        (*-monoˡ-<-pos (1/ max) (1/pos⇒pos {!  !} {!   !}) {!   !})
      N Nx Ny : ℕ
      Nx = proj₁ (ℝ.reg x ε/2max>0)
      Ny = proj₁ (ℝ.reg y ε/2max>0)
      N  = Nx ℕ.⊔ Ny
      helper₂ : (a b c : ℚ) → ∣ a ∣ ≤ max → ∣ b - c ∣ ≤ ε/2max →
        ∣ a ∣ · ∣ b - c ∣ ≤ ½ · ε
      helper₂ a b c p q = begin
        ∣ a ∣ · ∣ b - c ∣ ≡⟨ *-comm ∣ a ∣ ∣ b - c ∣ ⟩
        ∣ b - c ∣ · ∣ a ∣
          ≤⟨ *-monoˡ-≤-nonNeg ∣ b - c ∣ (nonNegative (0≤∣p∣ a)) p ⟩
        ∣ b - c ∣ · max
          ≤⟨ {!   !} ⟩
          -- ≤⟨ *-monoʳ-≤-nonNeg max (nonNegative (0≤∣p∣ (b - c))) q ⟩
        ½ · ε ÷ max · max      ≡⟨ {!   !} ⟩
        --½ · ε ÷ max · max      ≡⟨ *-assoc max (½ · ε) (1/ max) ⟩
        ½ · ε · (1/ max · max) ≡⟨ {!   !} ⟩
        --½ · ε · (1/ max · max) ≡⟨ cong (_·_ (½ · ε)) (*-inverseʳ max) ⟩
        ½ · ε · 1ℚ             ≡⟨ *-identityʳ (½ · ε) ⟩
        ½ · ε ∎

    unit ⦃ Mulℝ ⦄ = 1ℝ
    lemma-unit ⦃ Mulℝ ⦄ {x} = {!   !}


