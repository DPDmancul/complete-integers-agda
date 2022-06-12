
-- (c) Davide Peressoni 2022

{-# OPTIONS --without-K #-}

----------------------
-- Max  of function --
----------------------

open import Relation.Binary
open import Level

module Max
  {A B : Set}
  (non-empty : A)
  {_≤_ : Rel B 0ℓ}
  {_<_ : Rel B 0ℓ}
  (≤-<-connex : Connex _≤_ _<_)
  where
  open import Data.Product
  open import Data.Sum

  module _ (f : A → B) where

    private

      Th : Set
      Th = Σ[ i ∈ A ] ((j : A) → f j ≤ f i)

      module MaxMonad
        (⊥ : Set)
        where
        open import Monad ⊥ public

        oracle : (X : Set) → Prom X ⊎ ¬ X
        oracle X k = k (inj₂ λ x → k (inj₁ x))

        postulate
          -- We cannot wait for the result, and we are only
          -- interested in the existence of a result
          beforehand-escape : {X : Set} → Prom X → X

        {-# TERMINATING #-}
        go : A → Prom Th
        go j = oracle (Σ[ i ∈ A ] f j < f i) ⟫= helper
          where
          Help : A → Set
          Help j = Σ[ i ∈ A ] f j < f i
          helper : Help j ⊎ ¬ Help j → Prom Th
          helper (inj₁ (i , _)) = go i
          helper (inj₂ g)       = return (j , h)
            where
            h : (i : A) → f i ≤ f j
            h i with ≤-<-connex (f i) (f j)
            ... | inj₁ fi≤fj = fi≤fj
            ... | inj₂ fi>fj = beforehand-escape (⊥-elim (g (i , fi>fj)))

      open MaxMonad Th public

    maximum : Th
    maximum = escape (go non-empty)

