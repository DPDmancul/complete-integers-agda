
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe --without-K #-}

------------------
-- Real numbers --
------------------

module Data.R where
  open import Data.N hiding (_≤_ ; _<_ ; ∣_-_∣ ; _≟_) renaming (_>_ to _>ℕ_)
  open import Data.Q
  import Data.Int as ℤ
  import Data.Nat.Properties as ℕp
  import Data.Rational.Properties as ℚp
  open import Data.Product
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Agda.Builtin.Bool

  open import Ops

  record ℝ : Set where
    field
      seq : ℕ → ℚ
      reg : ∀ {ε : ℚ} → ε > 0ℚ → ∃[ N ] ∀ {n m : ℕ} → n >ℕ N → m >ℕ N →
        ∣ seq n - seq m ∣ ≤ ε

  fromℚ : ℚ → ℝ
  ℝ.seq (fromℚ q) _ = q
  ℝ.reg (fromℚ q) {ε} p = 0 , λ _ _ → begin
    ∣ q - q ∣ ≡⟨ cong ∣_∣ (ℚp.+-inverseʳ q) ⟩
    0ℚ        ≤⟨ ℚp.<⇒≤ p ⟩
    ε         ∎
    where open ℚp.≤-Reasoning


  0ℝ : ℝ
  0ℝ = fromℚ 0ℚ

  1ℝ : ℝ
  1ℝ = fromℚ 1ℚ

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
        ≡⟨ cong (λ z → ∣ (xn + yn) + z ∣) (ℚp.neg-distrib-+ xm ym) ⟩
      ∣ (xn + yn) + (- xm - ym) ∣
        ≡⟨ cong ∣_∣ (ℚp.+-assoc xn yn (- xm - ym)) ⟩
      ∣ xn + (yn + (- xm - ym)) ∣
        ≡⟨ cong (λ z → ∣ xn + z ∣) (sym (ℚp.+-assoc yn (- xm) (- ym))) ⟩
      ∣ xn + (yn - xm - ym) ∣
        ≡⟨ cong (λ z → ∣ xn + (z - ym) ∣) (ℚp.+-comm yn (- xm)) ⟩
      ∣ xn + (- xm + yn - ym) ∣
        ≡⟨ cong (λ z → ∣ xn + z ∣) (ℚp.+-assoc (- xm) yn (- ym)) ⟩
      ∣ xn + (- xm + (yn - ym)) ∣
        ≡⟨ cong ∣_∣ (sym (ℚp.+-assoc xn (- xm) (yn - ym))) ⟩
      ∣ (xn - xm) + (yn - ym) ∣ ≤⟨ ℚp.∣p+q∣≤∣p∣+∣q∣ (xn - xm) (yn - ym) ⟩
      ∣ xn - xm ∣ + ∣ yn - ym ∣
        ≤⟨ ℚp.+-mono-≤ (proj₂ (ℝ.reg x ε/2>0) (ℕp.<-transʳ (ℕp.m≤m⊔n Nx Ny) q)
                                              (ℕp.<-transʳ (ℕp.m≤m⊔n Nx Ny) r))
                       (proj₂ (ℝ.reg y ε/2>0) (ℕp.<-transʳ (ℕp.n≤m⊔n Nx Ny) q)
                                              (ℕp.<-transʳ (ℕp.n≤m⊔n Nx Ny) r)) ⟩
      ½ · ε + ½ · ε ≡⟨ sym (ℚp.*-distribʳ-+ ε ½ ½) ⟩
      1ℚ · ε        ≡⟨ ℚp.*-identityˡ ε ⟩
      ε             ∎
      where
      open ℚp.≤-Reasoning
      ε/2>0 : ½ · ε > 0ℚ
      ε/2>0 = ℚp.<-respˡ-≡ (ℚp.*-zeroˡ ε)
        (ℚp.*-monoˡ-<-pos ε (positive p) (*<* {0ℚ} {½} (ℤ.+<+ (s≤s z≤n))))
      N Nx Ny : ℕ
      Nx = proj₁ (ℝ.reg x ε/2>0)
      Ny = proj₁ (ℝ.reg y ε/2>0)
      N  = Nx Data.N.⊔ Ny

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
      ∣ xn · yn - xm · ym ∣ ≡⟨ {!   !} ⟩
      ∣ yn · (xn - xm) + xm · (yn - ym) ∣ ≤⟨ {!   !} ⟩
      ∣ yn · (xn - xm) ∣ + ∣ xm · (yn - ym) ∣ ≡⟨ {!   !} ⟩
      ∣ yn ∣ · ∣ xn - xm ∣ + ∣ xm ∣ · ∣ yn - ym ∣
        <⟨ ℚp.+-mono-< (helper yn xn xm {!   !}) (helper xm yn ym {!   !}) ⟩
      -- IF  yn = 0 OR xm = 0
      --  THEN it is trivial
      --  ELSE use max != 0
      -- ∣ yn ∣ · (½ · ε ÷ max) + ∣ xm ∣ · ∣ (½ · ε ÷ max) ∣ <⟨ {!   !} ⟩
      -- ∣ yn ∣ · (½ · ε ÷ ∣ yn ∣) + ∣ xm ∣ · ∣ (½ · ε ÷ ∣ xm ∣) ∣ ≡⟨ {!   !} ⟩
      ½ · ε + ½ · ε ≡⟨ sym (ℚp.*-distribʳ-+ ε ½ ½) ⟩
      1ℚ · ε        ≡⟨ ℚp.*-identityˡ ε ⟩
      ε             ∎
      where
      open ℚp.≤-Reasoning
      max = {!   !} -- max | seq n |
      -- TODO : find max != 0, if not then it is trivial
      ε/2max = ½ · ε ÷ max
      ε/2max>0 : ε/2max  > 0ℚ
      ε/2max>0 = {!   !}
      N Nx Ny : ℕ
      Nx = proj₁ (ℝ.reg x ε/2max>0)
      Ny = proj₁ (ℝ.reg y ε/2max>0)
      N  = Nx Data.N.⊔ Ny
      helper : (a b c : ℚ) → ∣ b - c ∣ < ε/2max → ∣ a ∣ · ∣ b - c ∣ < ½ · ε
      helper a b c p with does (a ≟ 0ℚ)
      ... | true  = {!   !}
      ... | false = {!   !}

    unit ⦃ Mulℝ ⦄ = 1ℝ
    lemma-unit ⦃ Mulℝ ⦄ {x} = {!   !}


