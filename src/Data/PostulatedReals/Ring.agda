
-- (c) Davide Peressoni 2022

{-# OPTIONS --without-K #-}

--------------------------------
-- Properteis of real numbers --
--------------------------------


module Data.PostulatedReals.Ring where

  open import Data.PostulatedReals.Core
  import Algebra.Properties.Ring
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import Data.Product
  open import Algebra
  open import Ops

  postulate
    *-neg-identityˡ : (x : ℝ) → -1ℝ · x ≡ - x

  private
    +-identityˡ = lemma-+-identityˡ
    *-identityˡ = lemma-*-identityˡ

    postulate
      +-comm : (x y : ℝ) → x + y ≡ y + x
      +-assoc : (x y z : ℝ) → (x + y) + z ≡ x + (y + z)

      +-inverseʳ : (x : ℝ) → x + (- x) ≡ additive-zero

      *-comm : (x y : ℝ) → x · y ≡ y · x
      *-assoc : (x y z : ℝ) → (x · y) · z ≡ x · (y · z)
      *-distribˡ-+ : (x y z : ℝ) → x · (y + z) ≡ (x · y) + (x · z)

      +-trans-≤ : (x y z : ℝ) → x ≤ y → x + z ≤ y + z
      *-trans-≤ : (x y : ℝ) → x ≥ 0ℝ → y ≥ 0ℝ → x · y ≥ 0ℝ

    +-identityʳ : (x : ℝ) → x + additive-zero ≡ x
    +-identityʳ x rewrite +-comm x additive-zero = +-identityˡ x

    +-inverseˡ : (x : ℝ) → (- x) + x ≡ additive-zero
    +-inverseˡ x rewrite +-comm (- x) x = +-inverseʳ x

    *-distribʳ-+ : (x y z : ℝ) → (y + z) · x ≡ (y · x) + (z · x)
    *-distribʳ-+ x y z rewrite *-comm (y + z) x | *-comm y x | *-comm z x =
      *-distribˡ-+ x y z

    *-identityʳ : (x : ℝ) → x · unit ≡ x
    *-identityʳ x rewrite *-comm x unit = *-identityˡ x

    *-zeroˡ : (x : ℝ) → additive-zero · x ≡ additive-zero
    *-zeroˡ x = begin
      0ℝ · x               ≡⟨ cong (_· x) (sym (+-inverseʳ 1ℝ)) ⟩
      (1ℝ + -1ℝ) · x       ≡⟨ *-distribʳ-+ x 1ℝ -1ℝ ⟩
      (1ℝ · x) + (-1ℝ · x) ≡⟨ cong₂ _+_ (*-identityˡ x) (*-neg-identityˡ x) ⟩
      x + (- x)            ≡⟨ +-inverseʳ x ⟩
      0ℝ ∎

    *-zeroʳ : (x : ℝ) → x · additive-zero ≡ additive-zero
    *-zeroʳ x rewrite *-comm x additive-zero = *-zeroˡ x

    ℝ-+-isMagma = record
      { isEquivalence = isEquivalence
      ; ∙-cong        =  cong₂ (_+_ ⦃ Sumℝ ⦄)
      }
    ℝ-*-isMagma = record
      { isEquivalence = isEquivalence
      ; ∙-cong        =  cong₂ (_·_ ⦃ Mulℝ ⦄)
      }

    ℝ-+-isSemigroup = record
      { isMagma = ℝ-+-isMagma
      ; assoc   = +-assoc
      }
    ℝ-*-isSemigroup = record
      { isMagma = ℝ-*-isMagma
      ; assoc   = *-assoc
      }

    ℝ-+-isMonoid = record
      { isSemigroup = ℝ-+-isSemigroup
      ; identity    = +-identityˡ , +-identityʳ
      }
    ℝ-*-isMonoid = record
      { isSemigroup = ℝ-*-isSemigroup
      ; identity    = *-identityˡ , *-identityʳ
      }

    ℝ-+-isGroup = record
      { isMonoid = ℝ-+-isMonoid
      ; inverse  = +-inverseˡ , +-inverseʳ
      ; ⁻¹-cong  = cong (-_)
      }

    ℝ-+-isAbelianGroup = record
      { isGroup = ℝ-+-isGroup
      ; comm    = +-comm
      }

    ℝ-isRing = record
      { +-isAbelianGroup = ℝ-+-isAbelianGroup
      ; *-isMonoid       = ℝ-*-isMonoid
      ; distrib          = *-distribˡ-+ , *-distribʳ-+
      ; zero             = *-zeroˡ , *-zeroʳ
      }

    ℝ-isCommRing = record
      { isRing = ℝ-isRing
      ; *-comm = *-comm
      }

  open IsCommutativeRing ℝ-isCommRing hiding (sym) public
  open Algebra.Properties.Ring record
    { Carrier = ℝ
    ; _≈_ = _≡_
    ; _+_ = _+_
    ; _*_ = _·_
    ; -_ = -_
    ; 0# = additive-zero
    ; 1# = unit
    ; isRing = ℝ-isRing
    } public
