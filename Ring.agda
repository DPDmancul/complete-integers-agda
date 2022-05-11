
-- (c) Davide Peressoni 2022

module Ring where

  open import Utils.Equality
  open import Ops

  ------------------------
  -- Commutative Monoid --
  ------------------------

  record CommMonoid (A : Set) (_•_ : A → A → A) (identity : A) : Set where
    field
      lemma-associative : {a b c : A} → (a • b) • c ≡ a • (b • c)
      lemma-commutative : {a b : A} → a • b ≡ b • a
      lemma-identity-left : {a : A} → identity • a ≡ a
    lemma-identity-right : {a : A} → a • identity ≡ a
    lemma-identity-right = trans lemma-commutative lemma-identity-left

  open CommMonoid ⦃ ... ⦄ public


  --------------------------
  -- Commutative Semiring --
  --------------------------

  record CommRig (A : Set) ⦃ _ : Sum A ⦄ ⦃ _ : Mul A ⦄ : Set where

    -- Commutative monoid
    field
      ⦃ comm-monoid-add ⦄ : CommMonoid A _+_ additive-zero
      ⦃ comm-monoid-mul ⦄ : CommMonoid A _·_ unit

    -- Multiplication distributive under addition
    field lemma-mul-left-distributive : {a b c : A} → a · (b + c) ≡ (a · b) + (a · c)
    lemma-mul-right-distributive : {a b c : A} → (b + c) · a ≡ (b · a) + (c · a)
    lemma-mul-right-distributive {a} {b} {c} = trans lemma-commutative
                                                       (trans lemma-mul-left-distributive
                                                              (cong2 _+_ lemma-commutative lemma-commutative))

    -- Multiplication by zero
    field lemma-mul-zero-left : {a : A} → additive-zero · a ≡ additive-zero
    lemma-mul-zero-right : {a : A} → a · additive-zero ≡ additive-zero
    lemma-mul-zero-right = trans lemma-commutative lemma-mul-zero-left

  open CommRig ⦃ ... ⦄ public


  ---------------------------------
  -- Commutative Ring with Unity --
  ---------------------------------

  record CommRing (A : Set) ⦃ _ : Sum A ⦄ ⦃ _ : Sub A ⦄ ⦃ _ : Mul A ⦄ : Set where

    field
      ⦃ comm-rig ⦄ : CommRig A
      lemma-additive-inverse : {a : A} → a + (- a) ≡ additive-zero

  open CommRing ⦃ ... ⦄ public
