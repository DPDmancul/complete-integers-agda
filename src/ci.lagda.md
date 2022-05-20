<!--
```agda
-- (c) Davide Peressoni 2022

open import Data.N
open import Data.Int
import Data.Integer.Properties as ℤp
open import Data.F2
import Data.F2.Properties as 𝔽₂p
open import Algebra
open import Relation.Binary.PropositionalEquality
```
-->

# Complete integer numbers

**TODO** sistemare  
In this chapter we will define the ring of complete integers ($\bZ_C$) and we will
see that it is a superset of $\bZ$. Then we will call the remaining dis-integers
($\bZ_D$) which are the dual of integers ($\bZ$) along parity (e.g. in $\bZ$ the unit is
odd, in $\bZ_D$ the unit is even).

::: {.definition name="Complete integers prime"}
Let's define the set of the complete integer numbers prime as

$$\bZ_C' \coloneqq \bZ\times\bF_2$$

We will call the first component \emph{value}, and the second \emph{parity}.

```agda
record ℤC' : Set where
  constructor [_,_]
  field
    val : ℤ
    par : 𝔽₂
```
:::

::: {.definition name="Ring $\bZ_C'$"}
Let's define $\bZ_C'$ as a commutative ring with unit:

Given $[a,b], [c,d] \in \bZ_C'$

$$[a,b] + [c,d] \coloneqq [a+c, b\oplus d]$$

```agda
instance
  open import Ops

  SumℤC' : Sum ℤC'
  _+_ ⦃ SumℤC' ⦄ [ a , b ] [ c , d ] = [ a + c , b ⊕ d ]
  additive-zero ⦃ SumℤC' ⦄ = [ 0ℤ , zero ]
  lemma-sum-zero ⦃ SumℤC' ⦄ = cong₂ [_,_] lemma-sum-zero lemma-sum-zero

  SubℤC' : Sub ℤC'
  -_ ⦃ SubℤC' ⦄ [ a , b ] = [ - a , b ]
```

$$[a,b] \cdot [c,d] \coloneqq [a\cdot c, b\cdot d]$$

```agda
instance
  open import Ops

  MulℤC' : Mul ℤC'
  _·_ ⦃ MulℤC' ⦄ [ a , b ] [ c , d ] = [ a · c , b · d ]
  unit ⦃ MulℤC' ⦄ = [ 1ℤ , one ]
  lemma-unit ⦃ MulℤC' ⦄ = cong₂ [_,_] lemma-unit lemma-unit
```
:::
::: {.proof}
  Now let's check if the given definition is valid:
```agda
module RingℤC' where

  ---------------------
  -- Properties of + --
  ---------------------

  +-assoc : (a b c : ℤC') → (a + b) + c ≡ a + (b + c)
  +-assoc [ va , pa ] [ vb , pb ] [ vc , pc ] =
    cong₂ [_,_] (ℤp.+-assoc va vb vc) (𝔽₂p.⊕-assoc pa pb pc)

  +-comm : (a b : ℤC') → a + b ≡ b + a
  +-comm [ va , pa ] [ vb , pb ] =
    cong₂ [_,_] (ℤp.+-comm va vb) (𝔽₂p.⊕-comm pa pb)

  +-identityˡ : (z : ℤC') → additive-zero + z ≡ z
  +-identityˡ _ = lemma-sum-zero
  +-identityʳ : (z : ℤC') → z + additive-zero ≡ z
  +-identityʳ z rewrite (+-comm z additive-zero) = +-identityˡ z

  +-inverseˡ : (z : ℤC') → (- z) + z ≡ additive-zero
  +-inverseˡ [ v , p ] = cong₂ [_,_] (ℤp.+-inverseˡ v) (𝔽₂p.⊕-self p)
  +-inverseʳ : (z : ℤC') → z + (- z) ≡ additive-zero
  +-inverseʳ [ v , p ] = cong₂ [_,_] (ℤp.+-inverseʳ v) (𝔽₂p.⊕-self p)

  ---------------------
  -- Properties of · --
  ---------------------

  ·-assoc : (a b c : ℤC') → (a · b) · c ≡ a · (b · c)
  ·-assoc [ va , pa ] [ vb , pb ] [ vc , pc ] =
    cong₂ [_,_] (ℤp.*-assoc va vb vc) (𝔽₂p.∧-assoc pa pb pc)

  ·-comm : (a b : ℤC') → a · b ≡ b · a
  ·-comm [ va , pa ] [ vb , pb ] =
    cong₂ [_,_] (ℤp.*-comm va vb) (𝔽₂p.∧-comm pa pb)

  ·-identityˡ : (z : ℤC') → unit · z ≡ z
  ·-identityˡ _ = lemma-unit
  ·-identityʳ : (z : ℤC') → z · unit ≡ z
  ·-identityʳ z rewrite (·-comm z unit) = ·-identityˡ z

  ·-distribʳ-+ : (c a b : ℤC') → (a + b) · c ≡ a · c + b · c
  ·-distribʳ-+ [ vc , pc ] [ va , pa ] [ vb , pb ] =
    cong₂ [_,_] (ℤp.*-distribʳ-+ vc va vb) (𝔽₂p.∧-distribʳ-⊕ pc pa pb)
  ·-distribˡ-+ : (c a b : ℤC') → c · (a + b) ≡ c · a + c · b
  ·-distribˡ-+ c a b rewrite (·-comm c (a + b)) rewrite  (·-distribʳ-+ c a b)=
    (cong₂ _+_  (·-comm a c) (·-comm b c))

  ·-zeroˡ : (a : ℤC') → additive-zero · a ≡ additive-zero
  ·-zeroˡ [ v , p ] = cong₂ [_,_] (ℤp.*-zeroˡ v)  (𝔽₂p.∧-zeroˡ p)
  ·-zeroʳ : (a : ℤC') → a · additive-zero ≡ additive-zero
  ·-zeroʳ a rewrite (·-comm a additive-zero) = ·-zeroˡ a

  ----------------
  -- Structures --
  ----------------

  ℤC'-+-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        =  cong₂ (_+_ ⦃ SumℤC' ⦄)
    }
  ℤC'-·-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        =  cong₂ (_·_ ⦃ MulℤC' ⦄)
    }

  ℤC'-+-isSemigroup = record
    { isMagma = ℤC'-+-isMagma
    ; assoc   = +-assoc
    }
  ℤC'-·-isSemigroup = record
    { isMagma = ℤC'-·-isMagma
    ; assoc   = ·-assoc
    }

  ℤC'-+-isMonoid = record
    { isSemigroup = ℤC'-+-isSemigroup
    ; identity    = +-identityˡ , +-identityʳ
    }
    where open import Agda.Builtin.Sigma
  ℤC'-·-isMonoid = record
    { isSemigroup = ℤC'-·-isSemigroup
    ; identity    = ·-identityˡ , ·-identityʳ
    }
    where open import Agda.Builtin.Sigma

  ℤC'-+-isGroup = record
    { isMonoid = ℤC'-+-isMonoid
    ; inverse  = +-inverseˡ , +-inverseʳ
    ; ⁻¹-cong  = cong (-_)
    }
    where open import Agda.Builtin.Sigma

  ℤC'-+-isAbelianGroup = record
    { isGroup = ℤC'-+-isGroup
    ; comm    = +-comm
    }

  ℤC'-isRing = record
    { +-isAbelianGroup = ℤC'-+-isAbelianGroup
    ; *-isMonoid       = ℤC'-·-isMonoid
    ; distrib          = ·-distribˡ-+ , ·-distribʳ-+
    ; zero             = ·-zeroˡ , ·-zeroʳ
    }
    where open import Agda.Builtin.Sigma

  ℤC'-isCommRing = record
    { isRing = ℤC'-isRing
    ; *-comm = ·-comm
    }
  ```
:::

::: {.lemma name="Powers of $\bZ_C'$"}
  $$[v,p]^n = [v^n,p]\quad\forall\ n\in\bN^+$$
  $$[v,p]^0 = [1,1]$$
:::
::: {.proof}
\   
```agda
lemma-ℤC'-powers : {z : ℤC'} {n : ℕ}
  → z ^ n ≡ [_,_] ((ℤC'.val z) ^ n) ((ℤC'.par z) ^ n)
lemma-ℤC'-powers {n = zero}    = refl
lemma-ℤC'-powers {z} {ℕ.suc n} = cong (λ z' → z · z') (lemma-ℤC'-powers {n = n})

lemma-ℤC'-powers-succ : {z : ℤC'} {n : ℕ}
  → z ^ ℕ.suc n ≡ [_,_] ((ℤC'.val z) ^ ℕ.suc n) (ℤC'.par z)
lemma-ℤC'-powers-succ {[ _ , p ]} {n}
  = trans (lemma-ℤC'-powers {n = ℕ.suc n}) (cong₂ [_,_] refl (𝔽₂p.pow p n))

lemma-ℤC'-powers-zero : {z : ℤC'} → z ^ zero ≡ unit
lemma-ℤC'-powers-zero = refl
```
:::

## Value and parity
In this section we will see two functions, that explain the role of $v$ and $p$,
and see their properties.

::: {.definition name="Value function"}
  $$\mathrm{val} \colon A \to \bZ$$
  $$\mathrm{val}(z) \coloneqq z \quad\forall\ z\in\bZ$$
  $$\mathrm{val}([v,p]) \coloneqq v \quad\forall\ [v,p]\in\bZ_C'$$
  Later on we will define this function for other sets $A$.

```agda
record Val (A : Set) : Set where
  field
    val : A → ℤ

open Val ⦃ ... ⦄

instance
  Valℤ : Val ℤ
  val ⦃ Valℤ ⦄ z = z

instance
  ValℤC' : Val ℤC'
  val ⦃ ValℤC' ⦄ = ℤC'.val
```
:::

::: {.theorem name="Properties of value"}
Given $x,y\in\bZ \lor x,y\in\bZ_C'$ and $z\in\bZ$

1. Value is odd.

  $$\mathrm{val}(-x) = -\mathrm{val}(x)$$

```agda
th-val-odd-ℤ : {x : ℤ} → val (- x) ≡ - val x
th-val-odd-ℤ = refl
th-val-odd-ℤC' : {x : ℤC'} → val (- x) ≡ - val x
th-val-odd-ℤC' = refl
```

2. Linearity.

  $$\mathrm{val}(x+y) = \mathrm{val}(x)+\mathrm{val}(y)$$
  $$\mathrm{val}(z\cdot x) = z\mathrm{val}(x)$$

```agda
th-val-linearity-+-ℤ : {x y : ℤ} → val (x + y) ≡ val x + val y
th-val-linearity-+-ℤ = refl

th-val-linearity-·-ℤ : {x z : ℤ} → val (z · x) ≡ z · val x
th-val-linearity-·-ℤ = refl


th-val-linearity-+-ℤC' : {x y : ℤC'} → val (x + y) ≡ val x + val y
th-val-linearity-+-ℤC' = refl

th-val-linearity-·ℕ-ℤC' : {x : ℤC'} {n : ℕ} → val (n × x) ≡ ℤ.pos n · val x
th-val-linearity-·ℕ-ℤC' {n = zero}    = refl
th-val-linearity-·ℕ-ℤC' {x} {ℕ.suc n} = begin
  val (ℕ.suc n × x)            ≡⟨⟩
  val (x + n × x)              ≡⟨ th-val-linearity-+-ℤC' {x} {n × x} ⟩
  val x + val (n × x)          ≡⟨ cong (λ y → val x + y)
                                  (th-val-linearity-·ℕ-ℤC' {x} {n}) ⟩
  val x + ℤ.pos n · val x      ≡⟨ cong (λ y → y + ℤ.pos n · val x)
                                       (sym (ℤp.*-identityˡ (val  x))) ⟩
  1ℤ · val x + ℤ.pos n · val x ≡⟨ sym (ℤp.*-distribʳ-+ (val x) 1ℤ (ℤ.pos n)) ⟩
  (1ℤ + ℤ.pos n) · val x       ≡⟨⟩
  ℤ.pos (ℕ.suc n) · val x      ∎
  where open ≡-Reasoning

th-val-linearity-·-ℤC' : {x : ℤC'} {z : ℤ} → val (z × x) ≡ z · val x
th-val-linearity-·-ℤC' {z = ℤ.pos n}  = cong val (th-val-linearity-·ℕ-ℤC' {n = n})
th-val-linearity-·-ℤC' {x} { -[1+ n ]} = begin
  val (-[1+ n ] × x)        ≡⟨⟩
  val (- (ℕ.suc n × x))     ≡⟨⟩
  - val (ℕ.suc n × x)       ≡⟨ cong (-_) (th-val-linearity-·ℕ-ℤC' {n = ℕ.suc n}) ⟩
  - (+[1+ n ] · val x)      ≡⟨ ℤp.neg-distribˡ-* +[1+ n ] (val x) ⟩
  (- +[1+ n ]) · val x      ≡⟨⟩
  -[1+ n ] · val x          ∎
  where open ≡-Reasoning
```

:::

