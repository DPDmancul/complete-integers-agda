<!--
```agda
-- (c) Davide Peressoni 2022

-- Copyright 2022 Davide Peressoni
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

open import Data.N
open import Data.Int hiding (∣_∣)
import Data.Int.Properties as ℤp
open import Data.F2
import Data.F2.Properties as 𝔽₂p
open import Algebra
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Function.Base
open import Even
open import Data.Empty
open import Data.Product hiding(_×_)
open import Data.PostulatedReals
import Data.PostulatedReals.Properties as ℝp
```
-->

# Complete integer numbers

In this chapter we will define the ring of complete integers ($\bZ_C$) and we
will see that it is a superset of $\bZ$. Then we will call the remaining
dis-integers ($\bZ_D$), which are the dual of integers ($\bZ$) along parity (e.g.
in $\bZ$ the unit is odd, in $\bZ_D$ the unit is even).

::: {.definition name="Complete integers"}
Let's define the set of the complete integer numbers as

\[\bZ_C \coloneqq \bZ\times\bF_2\]

We will call the first component _value_, and the second _parity_.

```agda
record ℤC : Set where
  constructor [_,_]
  field
    val : ℤ
    par : 𝔽₂
```
:::

::: {.definition name="Ring of complete integers "}
Let's define $\bZ_C$ as a commutative ring with unit:

Given $[a,b], [c,d] \in \bZ_C$

\[[a,b] + [c,d] \coloneqq [a+c, b\oplus d]\]

```agda
instance
  open import Ops

  SumℤC : Sum ℤC
  _+_ ⦃ SumℤC ⦄ [ a , b ] [ c , d ] = [ a + c , b ⊕ d ]
  additive-zero ⦃ SumℤC ⦄ = [ 0ℤ , zero ]
  lemma-sum-zero ⦃ SumℤC ⦄ = cong₂ [_,_] lemma-sum-zero lemma-sum-zero

  SubℤC : Sub ℤC
  -_ ⦃ SubℤC ⦄ [ a , b ] = [ - a , b ]
```

\[[a,b] \cdot [c,d] \coloneqq [a\cdot c, b\cdot d]\]

```agda
instance
  open import Ops

  MulℤC : Mul ℤC
  _·_ ⦃ MulℤC ⦄ [ a , b ] [ c , d ] = [ a · c , b · d ]
  unit ⦃ MulℤC ⦄ = [ 1ℤ , one ]
  lemma-unit ⦃ MulℤC ⦄ = cong₂ [_,_] lemma-unit lemma-unit
```
:::
::: {.proof}
  Now let's check if the given definition is valid:
```agda
module RingℤC where

  ---------------------
  -- Properties of + --
  ---------------------

  +-assoc : (a b c : ℤC) → (a + b) + c ≡ a + (b + c)
  +-assoc [ va , pa ] [ vb , pb ] [ vc , pc ] =
    cong₂ [_,_] (ℤp.+-assoc va vb vc) (𝔽₂p.⊕-assoc pa pb pc)

  +-comm : (a b : ℤC) → a + b ≡ b + a
  +-comm [ va , pa ] [ vb , pb ] =
    cong₂ [_,_] (ℤp.+-comm va vb) (𝔽₂p.⊕-comm pa pb)

  +-identityˡ : (z : ℤC) → additive-zero + z ≡ z
  +-identityˡ _ = lemma-sum-zero
  +-identityʳ : (z : ℤC) → z + additive-zero ≡ z
  +-identityʳ z rewrite +-comm z additive-zero = +-identityˡ z

  +-inverseˡ : (z : ℤC) → (- z) + z ≡ additive-zero
  +-inverseˡ [ v , p ] = cong₂ [_,_] (ℤp.+-inverseˡ v) (𝔽₂p.⊕-self p)
  +-inverseʳ : (z : ℤC) → z + (- z) ≡ additive-zero
  +-inverseʳ [ v , p ] = cong₂ [_,_] (ℤp.+-inverseʳ v) (𝔽₂p.⊕-self p)

  ---------------------
  -- Properties of · --
  ---------------------

  ·-assoc : (a b c : ℤC) → (a · b) · c ≡ a · (b · c)
  ·-assoc [ va , pa ] [ vb , pb ] [ vc , pc ] =
    cong₂ [_,_] (ℤp.*-assoc va vb vc) (𝔽₂p.∧-assoc pa pb pc)

  ·-comm : (a b : ℤC) → a · b ≡ b · a
  ·-comm [ va , pa ] [ vb , pb ] =
    cong₂ [_,_] (ℤp.*-comm va vb) (𝔽₂p.∧-comm pa pb)

  ·-identityˡ : (z : ℤC) → unit · z ≡ z
  ·-identityˡ _ = lemma-unit
  ·-identityʳ : (z : ℤC) → z · unit ≡ z
  ·-identityʳ z rewrite ·-comm z unit = ·-identityˡ z

  ·-distribʳ-+ : (c a b : ℤC) → (a + b) · c ≡ a · c + b · c
  ·-distribʳ-+ [ vc , pc ] [ va , pa ] [ vb , pb ] =
    cong₂ [_,_] (ℤp.*-distribʳ-+ vc va vb) (𝔽₂p.∧-distribʳ-⊕ pc pa pb)
  ·-distribˡ-+ : (c a b : ℤC) → c · (a + b) ≡ c · a + c · b
  ·-distribˡ-+ c a b rewrite ·-comm c (a + b) | ·-distribʳ-+ c a b =
    (cong₂ _+_  (·-comm a c) (·-comm b c))

  ·-zeroˡ : (a : ℤC) → additive-zero · a ≡ additive-zero
  ·-zeroˡ [ v , p ] = cong₂ [_,_] (ℤp.*-zeroˡ v)  (𝔽₂p.∧-zeroˡ p)
  ·-zeroʳ : (a : ℤC) → a · additive-zero ≡ additive-zero
  ·-zeroʳ a rewrite ·-comm a additive-zero = ·-zeroˡ a

  ----------------
  -- Structures --
  ----------------

  ℤC-+-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        =  cong₂ (_+_ ⦃ SumℤC ⦄)
    }
  ℤC-·-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        =  cong₂ (_·_ ⦃ MulℤC ⦄)
    }

  ℤC-+-isSemigroup = record
    { isMagma = ℤC-+-isMagma
    ; assoc   = +-assoc
    }
  ℤC-·-isSemigroup = record
    { isMagma = ℤC-·-isMagma
    ; assoc   = ·-assoc
    }

  ℤC-+-isMonoid = record
    { isSemigroup = ℤC-+-isSemigroup
    ; identity    = +-identityˡ , +-identityʳ
    }
    where open import Agda.Builtin.Sigma
  ℤC-·-isMonoid = record
    { isSemigroup = ℤC-·-isSemigroup
    ; identity    = ·-identityˡ , ·-identityʳ
    }
    where open import Agda.Builtin.Sigma

  ℤC-+-isGroup = record
    { isMonoid = ℤC-+-isMonoid
    ; inverse  = +-inverseˡ , +-inverseʳ
    ; ⁻¹-cong  = cong (-_)
    }
    where open import Agda.Builtin.Sigma

  ℤC-+-isAbelianGroup = record
    { isGroup = ℤC-+-isGroup
    ; comm    = +-comm
    }

  ℤC-isRing = record
    { +-isAbelianGroup = ℤC-+-isAbelianGroup
    ; *-isMonoid       = ℤC-·-isMonoid
    ; distrib          = ·-distribˡ-+ , ·-distribʳ-+
    ; zero             = ·-zeroˡ , ·-zeroʳ
    }
    where open import Agda.Builtin.Sigma

  ℤC-isCommRing = record
    { isRing = ℤC-isRing
    ; *-comm = ·-comm
    }
  ```
:::

::: {.lemma name="Powers of complete integers"}
  \[[v,p]^n = [v^n,p]\quad\forall\ n\in\bN^+\]
  \[[v,p]^0 = [1,1]\]
:::
::: {.proof}
\
```agda
lemma-ℤC-powers : {z : ℤC} {n : ℕ}
  → z ^ n ≡ [ (ℤC.val z) ^ n , (ℤC.par z) ^ n ]
lemma-ℤC-powers {n = zero}    = refl
lemma-ℤC-powers {z} {ℕ.suc n} = cong (_·_ z) $ lemma-ℤC-powers {n = n}

lemma-ℤC-powers-succ : {z : ℤC} {n : ℕ}
  → z ^ ℕ.suc n ≡ [ (ℤC.val z) ^ ℕ.suc n , ℤC.par z ]
lemma-ℤC-powers-succ {[ _ , p ]} {n}
  = trans (lemma-ℤC-powers {n = ℕ.suc n}) (cong₂ [_,_] refl (𝔽₂p.pow p n))

lemma-ℤC-powers-zero : {z : ℤC} → z ^ zero ≡ unit
lemma-ℤC-powers-zero = refl
```
:::

## Value and parity
In this section we will see two functions, that explain the role of $v$ and $p$,
and see their properties.

::: {.definition name="Value function"}
  \[\val \colon \bZ \cup \bZ_C \to \bZ\]
  \[\val(z) \coloneqq z \quad\forall\ z\in\bZ\]
  \[\val([v,p]) \coloneqq v \quad\forall\ [v,p]\in\bZ_C\]

```agda
record Val (A : Set) : Set where
  field
    val : A → ℤ

open Val ⦃ ... ⦄

instance
  Valℤ : Val ℤ
  val ⦃ Valℤ ⦄ z = z

instance
  ValℤC : Val ℤC
  val ⦃ ValℤC ⦄ = ℤC.val
```
:::

::: {.theorem name="Properties of value"}
Given $x,y\in\bZ \lor x,y\in\bZ_C$ and $z\in\bZ$

1. Value is odd.

  \[\val(-x) = -\val(x)\]

```agda
th-val-odd-ℤ : {x : ℤ} → val (- x) ≡ - val x
th-val-odd-ℤ = refl

th-val-odd-ℤC : {x : ℤC} → val (- x) ≡ - val x
th-val-odd-ℤC = refl
```

2. Linearity.

  \[\val(x+y) = \val(x)+\val(y)\]
  \[\val(z\cdot x) = z\val(x)\]

```agda
th-val-linearity-ℤ : {x y : ℤ} → val (x + y) ≡ val x + val y
th-val-linearity-ℤ = refl

th-val-homogeneity-ℤ : {x z : ℤ} → val (z · x) ≡ z · val x
th-val-homogeneity-ℤ = refl


th-val-linearity-ℤC : {x y : ℤC} → val (x + y) ≡ val x + val y
th-val-linearity-ℤC = refl

th-val-homogeneityℕ-ℤC : {x : ℤC} {n : ℕ} → val (n × x) ≡ ℤ.pos n · val x
th-val-homogeneityℕ-ℤC {n = zero}    = refl
th-val-homogeneityℕ-ℤC {x} {ℕ.suc n} = begin
  val (ℕ.suc n × x)            ≡⟨⟩
  val (x + n × x)              ≡⟨ th-val-linearity-ℤC {x} {n × x} ⟩
  val x + val (n × x)          ≡⟨ cong (_+_ (val x)) $
                                  th-val-homogeneityℕ-ℤC {x} {n} ⟩
  val x + ℤ.pos n · val x      ≡⟨ cong (_+ ℤ.pos n · val x) $
                                       sym (ℤp.*-identityˡ (val  x)) ⟩
  1ℤ · val x + ℤ.pos n · val x ≡˘⟨ ℤp.*-distribʳ-+ (val x) 1ℤ (ℤ.pos n) ⟩
  (1ℤ + ℤ.pos n) · val x       ≡⟨⟩
  ℤ.pos (ℕ.suc n) · val x      ∎

th-val-homogeneity-ℤC : {x : ℤC} {z : ℤ} → val (z × x) ≡ z · val x
th-val-homogeneity-ℤC {z = ℤ.pos n}  = cong val (th-val-homogeneityℕ-ℤC {n = n})
th-val-homogeneity-ℤC {x} { -[1+ n ]} = begin
  val (-[1+ n ] × x)        ≡⟨⟩
  val (- (ℕ.suc n × x))     ≡⟨⟩
  - val (ℕ.suc n × x)       ≡⟨ cong (-_) $ th-val-homogeneityℕ-ℤC {n = ℕ.suc n} ⟩
  - (+[1+ n ] · val x)      ≡⟨ ℤp.neg-distribˡ-* +[1+ n ] (val x) ⟩
  (- +[1+ n ]) · val x      ≡⟨⟩
  -[1+ n ] · val x          ∎
```

3. Idempotence of the value.

  \[\val\circ\val=\val\]

```agda
th-val-idempotence : {A : Set} ⦃ _ : Val A ⦄ {x : A} → val (val x) ≡ val x
th-val-idempotence = refl
```

4. Completely multiplicative.

  \[\val(1)=\val([1,1])=1\]
  \[\val(x\cdot y) = \val(x) \cdot \val(y)\]

```agda
th-val-mul-unit-ℤ : val {ℤ} unit ≡ 1ℤ
th-val-mul-unit-ℤ = refl

th-val-mul-unit-ℤC : val {ℤC} unit ≡ 1ℤ
th-val-mul-unit-ℤC = refl

th-val-mul-ℤ : {x y : ℤ} → val (x · y) ≡ val x · val y
th-val-mul-ℤ = refl

th-val-mul-ℤC : {x y : ℤC} → val (x · y) ≡ val x · val y
th-val-mul-ℤC = refl
```

:::

::: {.definition name="Parity function"}
  \[\Par \colon \bZ \cup \bZ_C \to \bF_2\]
  $$\Par(z) \coloneqq \begin{cases}
    0 & z\text{ even}\\
    1 & z\text{ odd}\\
  \end{cases} \quad\forall\ z\in\bZ$$
  \[\Par([v,p]) \coloneqq p \quad\forall\ [v,p]\in\bZ_C\]

```agda
record Par (A : Set) : Set where
  field
    par : A → 𝔽₂

open Par  ⦃ ... ⦄

instance
  Parℤ : Par ℤ
  par ⦃ Parℤ ⦄ z with even-or-odd z
  ... | even _ = zero
  ... | odd  _ = one

instance
  ParℤC : Par ℤC
  par ⦃ ParℤC ⦄ = ℤC.par
```
:::

A useful lemma for future proofs on parity in $\bZ$

```agda
parity-even : {z : ℤ} → Even z → par z ≡ zero
parity-even p rewrite lemma-even p = refl

parity-odd : {z : ℤ} → Odd z → par z ≡ one
parity-odd p rewrite lemma-odd p = refl
```

::: {.theorem name="Properties of parity"}
Given $x,y\in\bZ \lor x,y\in\bZ_C$ and $z\in\bZ$

1. Parity is even.

  \[\Par(-x) = \Par(x)\]

```agda
th-par-even-ℤ : {x : ℤ} → par (- x) ≡ par x
th-par-even-ℤ {x} with even-or-odd x
... | even p = parity-even (neg-even p)
... | odd  p = parity-odd (neg-odd p)

th-par-even-ℤC : {x : ℤC} → par (- x) ≡ par x
th-par-even-ℤC = refl
```

2. Linearity.

  Since $\Par(x)\in\bF_2$ the sum operator must be replaced by exclusive or
  ($\oplus$).

  \[\Par(x+y) = \Par(x) \oplus \Par(y)\]

```agda
th-par-linearity-ℤ : {x y : ℤ} → par (x + y) ≡ par x ⊕ par y
th-par-linearity-ℤ {x} {y} with even-or-odd x | even-or-odd y
... | even p | even q = parity-even $ sum-even-even p q
... | even p | odd  q = parity-odd  $ sum-even-odd  p q
... | odd  p | even q = parity-odd  $ sum-odd-even  p q
... | odd  p | odd  q = parity-even $ sum-odd-odd   p q


th-par-linearity-ℤC : {x y : ℤC} → par (x + y) ≡ par x ⊕ par y
th-par-linearity-ℤC = refl
```

3. Idempotence of the parity.

  \[\Par\circ\Par = \Par\]

  To prove this we need to extend the parity to $\bF_2$ (Agda does not know
  $\bF_2 \subset \bZ$)

```agda
instance
  Par𝔽₂ : Par 𝔽₂
  par ⦃ Par𝔽₂ ⦄ zero = par 0ℤ
  par ⦃ Par𝔽₂ ⦄ one  = par 1ℤ
```

```agda
th-par-idempotence : {A : Set} ⦃ _ : Par A ⦄ {x : A} → par (par x) ≡ par x
th-par-idempotence {x = x} with par x
... | zero = refl
... | one  = refl
```

4. Completely multiplicative.

  \[\Par(1) = 1\]
  \[\Par(x\cdot y) = \Par(x) \cdot \Par(y)\]

```agda
th-par-mul-unit-ℤ : par {ℤ} unit ≡ one
th-par-mul-unit-ℤ = refl

th-par-mul-unit-ℤC : par {ℤC} unit ≡ one
th-par-mul-unit-ℤC = refl

th-par-mul-ℤ : {x y : ℤ} → par (x · y) ≡ par x · par y
th-par-mul-ℤ {x} {y} with even-or-odd x | even-or-odd y
... | even p | even q = parity-even $ mul-even-even p q
... | even p | odd  q = parity-even $ mul-even-odd  p q
... | odd  p | even q = parity-even $ mul-odd-even  p q
... | odd  p | odd  q = parity-odd  $ mul-odd-odd   p q

th-par-mul-ℤC : {x y : ℤC} → par (x · y) ≡ par x · par y
th-par-mul-ℤC = refl
```
:::

::: {.lemma name="Parity of powers"}

\[\Par(z^n) = \Par(z) \quad \forall\ n\in\bN^+\]

:::
::: {.proof}
\
```agda
par-pow-ℤ : {z : ℤ} {n : ℕ} → par (z ^ ℕ.suc n) ≡ par z
par-pow-ℤ {z} {0} rewrite ℤp.*-identityʳ z = refl
par-pow-ℤ {z} {ℕ.suc n}  = begin
  par (z ^ ℕ.suc (ℕ.suc n)) ≡⟨⟩
  par (z · z ^ ℕ.suc n)     ≡⟨ th-par-mul-ℤ {z} {z ^ ℕ.suc n} ⟩
  par z · par (z ^ ℕ.suc n) ≡⟨ cong (_·_ (par z)) $ par-pow-ℤ {z} {n} ⟩
  par z · par z             ≡⟨ 𝔽₂p.∧-idem (par z) ⟩
  par z                     ∎

par-pow-ℤC : {z : ℤC} {n : ℕ} → par (z ^ ℕ.suc n) ≡ par z
par-pow-ℤC {z} {0}       = 𝔽₂p.∧-identityʳ (par z)
par-pow-ℤC {z} {ℕ.suc n} = begin
  par (z ^ ℕ.suc (ℕ.suc n)) ≡⟨⟩
  par (z · z ^ ℕ.suc n)     ≡⟨ th-par-mul-ℤC {z} {z ^ ℕ.suc n} ⟩
  par z · par (z ^ ℕ.suc n) ≡⟨ cong (_·_ (par z)) $ par-pow-ℤC {z} {n} ⟩
  par z · par z             ≡⟨ 𝔽₂p.∧-idem (par z) ⟩
  par z                     ∎
```
:::

## Related sets

::: {.definition name="Integers prime"}
Let us define the set of integers prime as

\[\bZ' \coloneqq \left\{[v,p]\in\bZ_C \colon p = \Par(v)\right\} =
\left\{[v,\Par(v)] \colon v\in\bZ\right\}\]

```agda
ℤ' : Set
ℤ' = Σ[ ([ v , p ]) ∈ ℤC ] p ≡ par v

ℤ'-eq : {a b : ℤ'} → proj₁ a ≡ proj₁ b → a ≡ b
ℤ'-eq {_ , refl} {_ , refl} refl = refl
```
:::

::: {.definition name="Dis-integers"}
Let us define the set of dis-integers as

\[\bZ_D \coloneqq \left\{[v,p]\in\bZ_C \colon p \neq \Par(v)\right\}\]

```agda
ℤD : Set
ℤD = Σ[ ([ v , p ]) ∈ ℤC ] p ≡ ¬ (par v)
```
:::

::: {.remark}
$\{ \bZ', \bZ_D\}$ is a partition of $\bZ_C$.
\[\bZ' \sqcup \bZ_D = \bZ_C\]
:::

::: {.theorem name="Integers and integers prime are isomorphic"}
The function $f_\bZ \colon \bZ \to \bZ'$ defined as
\[f_\bZ(z) = [z, \Par(z)]\]
is an isomorphism.

```agda
fℤ : ℤ → ℤ'
fℤ z = [ z , par z ] , refl

fℤ⁻¹ : ℤ' → ℤ
fℤ⁻¹ ([ z , _ ] , _) = z
```
:::
::: {.proof}
Before proving this we have to say to Agda to use on $\bZ'$ the same operations
of $\bZ_C$

```agda
instance
  Sumℤ' : Sum ℤ'
  _+_ ⦃ Sumℤ' ⦄ (a , refl) (b , refl) =
    a + b , sym (th-par-linearity-ℤ {val a})
  additive-zero  ⦃ Sumℤ' ⦄ = additive-zero , refl
  lemma-sum-zero ⦃ Sumℤ' ⦄ {[ v , _ ] , refl} =
    ℤ'-eq (cong [_, par v ] $ lemma-sum-zero {ℤ})

  Mulℤ' : Mul ℤ'
  _·_ ⦃ Mulℤ' ⦄ (a , refl) (b , refl) =
    a · b , sym (th-par-mul-ℤ {val a})
  unit       ⦃ Mulℤ' ⦄ = unit , refl
  lemma-unit ⦃ Mulℤ' ⦄ {[ v , _ ] , refl} =
    ℤ'-eq (cong [_, par v ] $ lemma-unit {ℤ})
```

```agda
module isomorphism-fℤ where

  ---------------------
  -- fℤ homomorphism --
  ---------------------

  addition : {a b : ℤ} → fℤ (a + b) ≡ fℤ a + fℤ b
  addition {a} {b} rewrite sym $ th-par-linearity-ℤ {a} {b} = refl

  multiplication : {a b : ℤ} → fℤ (a · b) ≡ fℤ a · fℤ b
  multiplication {a} {b} rewrite sym $ th-par-mul-ℤ {a} {b} = refl

  mul-identity : fℤ unit ≡ unit
  mul-identity = refl

  --------------------
  -- fℤ isomorphism --
  --------------------

  fℤ∘fℤ⁻¹≡id : {z : ℤ'} → fℤ (fℤ⁻¹ z) ≡ z
  fℤ∘fℤ⁻¹≡id {[ v , _ ] , refl} = ℤ'-eq refl

  fℤ⁻¹∘fℤ≡id : {z : ℤ} → fℤ⁻¹ (fℤ z) ≡ z
  fℤ⁻¹∘fℤ≡id = refl
```
:::

Since $\bZ'$ is isomorphic to $\bZ$, and so the two cannot be distinguished, we
won't write $\bZ'$ anymore and we will use the notation $[v, \Par(v)]$ to denote
elements in $\bZ$ too.

More precisely we will write, with an abuse of notation, $\bZ'=\bZ$ and $[v,
\Par(v)] = v$ meaning respectively $\bZ'=f_{\bZ}(\bZ)$ and $[v, \Par(v)] =
f_{\bZ}(v)$.

### Dis-integers

We said in the introduction that dis-integers are the dual of integers along
parity, in fact in $\bZ_D$ we have $[0,1]$ which has null value and odd parity,
$[1,0]$ which has unitary value, but even parity, and in general $[v,p]$ where
the parity $p$ is not the parity of the integer $v$.

::: {.definition name="Odd zero"}
Let's call $o \coloneqq [0,1]$ the _odd zero_, since it has null value and
odd parity.

```agda
o : ℤC
o = [ 0ℤ , one ]
```
:::

::: {.lemma name="Swap parity"}
Summing the odd zero to a complete integer its parity changes.
:::
::: {.proof}
\
```agda
swap-parity : (z : ℤC) → par z ≡ ¬ (par (z + o))
swap-parity [ _ , zero ] = refl
swap-parity [ _ , one  ] = refl
```
:::

::: {.definition name="Even unit"}
Let's call $l \coloneqq [1,0]$ the _even unit_, since it has unitary value and
even parity.

```agda
l : ℤC
l = [ 1ℤ , zero ]
```
:::

::: {.lemma name="Change only value"}
Summing the even unit to a complete integer only it's value changes, not its
parity.
:::
::: {.proof}
\
```agda
par[z+l] : (z : ℤC) → par (z + l) ≡ par z
par[z+l] [ _ , zero ] = refl
par[z+l] [ _ , one  ] = refl

val[z+l] : (z : ℤC) → val (z + l) ≡ val z + 1ℤ
val[z+l] [ v , _ ] = refl

par[z-l] : (z : ℤC) → par (z - l) ≡ par z
par[z-l] [ _ , zero ] = refl
par[z-l] [ _ , one  ] = refl

val[z-l] : (z : ℤC) → val (z - l) ≡ val z - 1ℤ
val[z-l] [ v , _ ] = refl
```
:::

::: {.lemma #ZD-from-Z name="Dis-integer as integer plus odd unit"}
Each dis-integer can be written as the sum of an integer with $l$.
:::
::: {.proof}
\
```agda
ℤD-from-ℤ+l : ((a , _) : ℤD) → Σ[ (b , _) ∈ ℤ' ] a ≡ b + l
ℤD-from-ℤ+l (a , q) = (a - l , help₁ (a , q)) , help₂ a
  where
  help₁ : ((z , _) : ℤD) → par (z - l) ≡ par (val (z - l))
  help₁ (z@([ v , _ ]) , refl) rewrite par[z-l] z
    | th-par-linearity-ℤ {v} { - 1ℤ} with par v
  ... | zero = refl
  ... | one  = refl
  help₂ : (z : ℤC) → z ≡ (z - l) + l
  help₂ z rewrite val[z-l] z | par[z-l] z | val[z+l] (z - l) | par[z+l] (z - l) =
    cong₂ [_,_] (sym $ trans (ℤp.+-assoc (val z) (- 1ℤ) 1ℤ)
                             (ℤp.+-identityʳ (val z)))
                (𝔽₂p.⊕-comm zero (par z))
```
:::

## Behaviours induced by parity

We now will show how the parity of a complete integer is not a mere binary flag,
but induces the same properties of even and odd numbers into $\bZ_C$: complete
integers with even parity act like even numbers and those with odd parity like
odd numbers.

```agda
data ℤC-Even : ℤC → Set where
  even : {z : ℤC} → par z ≡ zero → ℤC-Even z

data ℤC-Odd : ℤC → Set where
  odd : {z : ℤC} → par z ≡ one → ℤC-Odd z
```

::: {.lemma name="Parity of integers is preserved"}
The usual notion of parity in $\bZ$ and this new notion of parity in $\bZ_C$ are
the same for integer numbers.
:::
::: {.proof}
\
```agda
evenℤ⇒evenℤC : {z : ℤ} → Even z → ℤC-Even (proj₁ (fℤ z))
evenℤ⇒evenℤC p = even (parity-even p)

oddℤ⇒oddℤC : {z : ℤ} → Odd z → ℤC-Odd (proj₁ (fℤ z))
oddℤ⇒oddℤC p = odd (parity-odd p)

evenℤC⇒evenℤ : {z : ℤ'} → ℤC-Even (proj₁ z) → Even (fℤ⁻¹ z)
evenℤC⇒evenℤ {z} (even _) rewrite proj₂ z with even-or-odd (fℤ⁻¹ z)
... | even q = q

oddℤC⇒oddℤ : {z : ℤ'} → ℤC-Odd (proj₁ z) → Odd (fℤ⁻¹ z)
oddℤC⇒oddℤ {z} (odd _) rewrite proj₂ z with even-or-odd (fℤ⁻¹ z)
... | odd q = q
```
:::

::: {.lemma name="Parity of addition"}
\[\mathrm{even} + \mathrm{even} = \mathrm{even}\]
\[\mathrm{even} + \mathrm{odd} = \mathrm{odd}\]
\[\mathrm{odd} + \mathrm{even} = \mathrm{odd}\]
\[\mathrm{odd} + \mathrm{odd} = \mathrm{even}\]
:::
::: {.proof}
\
```agda
sum-ℤC-even-even : {x y : ℤC} → ℤC-Even x → ℤC-Even y → ℤC-Even (x + y)
sum-ℤC-even-even (even refl) (even refl) = even refl

sum-ℤC-even-odd : {x y : ℤC} → ℤC-Even x → ℤC-Odd y → ℤC-Odd (x + y)
sum-ℤC-even-odd (even refl) (odd refl) = odd refl

sum-ℤC-odd-even : {x y : ℤC} → ℤC-Odd x → ℤC-Even y → ℤC-Odd (x + y)
sum-ℤC-odd-even (odd refl) (even refl) = odd refl

sum-ℤC-odd-odd : {x y : ℤC} → ℤC-Odd x → ℤC-Odd y → ℤC-Even (x + y)
sum-ℤC-odd-odd (odd refl) (odd refl) = even refl
```
:::

::: {.lemma name="Parity of multiplication"}
\[\mathrm{even} \cdot \mathrm{even} = \mathrm{even}\]
\[\mathrm{even} \cdot \mathrm{odd} = \mathrm{even}\]
\[\mathrm{odd} \cdot \mathrm{even} = \mathrm{even}\]
\[\mathrm{odd} \cdot \mathrm{odd} = \mathrm{odd}\]
:::
::: {.proof}
\
```agda
mul-ℤC-even-even : {x y : ℤC} → ℤC-Even x → ℤC-Even y → ℤC-Even (x · y)
mul-ℤC-even-even (even refl) (even refl) = even refl

mul-ℤC-even-odd : {x y : ℤC} → ℤC-Even x → ℤC-Odd y → ℤC-Even (x · y)
mul-ℤC-even-odd (even refl) (odd refl) = even refl

mul-ℤC-odd-even : {x y : ℤC} → ℤC-Odd x → ℤC-Even y → ℤC-Even (x · y)
mul-ℤC-odd-even (odd refl) (even refl) = even refl

mul-ℤC-odd-odd : {x y : ℤC} → ℤC-Odd x → ℤC-Odd y → ℤC-Odd (x · y)
mul-ℤC-odd-odd (odd refl) (odd refl) = odd refl
```
:::

## Reals exponentiation to the power of complete integers

In this section we will define an exponentiation function with real bases and
complete integer exponents.

To help us come up with a good definition we can split on the exponent $z$:

1. If $z$ is an integer, this operation is already defined as $x^z$ for
   $x\in\bR$;
2. If $z$ is a dis-integer, we know from lemma \@ref(lem:ZD-from-Z) that there
   exist an integer $y = z - l$ s.t. $z = y + l$; supposing that our function
   respects exponent rules (which we will prove in theorem
   \@ref(thm:exponent-rules)), we can write $x^z = z^{y+l} = z^y \cdot z^l$.

So all we have to do is to define the value of $x^l$.

If we pick an $x \in \bR$ we can intuitively say that $x^l$ should be equal to
$|x|$ because:

1. being the parity of $l$ even, $x^l$ should be an even function of $x$;
2. being the value of $l$ one, $x^l$ should be a somewhat linear function.

So our definition, for $x\in\bR$ and $z\in\bZ_C$, would be:
\[x^z = \begin{cases}\text{usual }x^z & z\in\bZ \\
  x^y \cdot x^l = x^y \cdot |x| & z\in\bZ_D \end{cases}\]
with $y = z - l \in\bZ$

We will instead use another definition, and later prove they are equal.

::: {.definition #real-powers name="Real exponentiation to complete integers"}
For $x\in\bR$ and $z\in\bZ_C$, we define
\[x^z = x^{\val(z) - k} |x|^k\]
with $k = \Par\left(\val(z)\right) \oplus \Par(z)$.

```agda
𝔽₂-to-ℤ : 𝔽₂ → ℤ
𝔽₂-to-ℤ zero = 0ℤ
𝔽₂-to-ℤ one  = 1ℤ

instance
  CIPowℝ\0 : Pow ℝ\0 ℤC {ℝ}
  _^_ ⦃ CIPowℝ\0 ⦄ x [ v , p ] = let k = 𝔽₂-to-ℤ (par v ⊕ p) in
    x ^ (v - k) · ∣ x ∣₀ ^ k
```
:::
::: {.proof}
\
```agda
pow-def-eq-ℤ : (z : ℤ) → (x : ℝ\0) → x ^ proj₁ (fℤ z) ≡ x ^ z
pow-def-eq-ℤ z x rewrite 𝔽₂p.⊕-self (par z) | ℤp.+-identityʳ z
  | ℝp.ℝ\0^0 ∣ x ∣₀ = ℝp.*-identityʳ (x ^ z)

pow-def-eq-ℤD : (z : ℤD) → (x : ℝ\0) → let y = fℤ⁻¹ (proj₁ (ℤD-from-ℤ+l z)) in
  x ^ proj₁ z ≡ x ^ y · ∣ ℝ∪0 x ∣
pow-def-eq-ℤD ([ v , _ ] , refl) x rewrite sym (𝔽₂p.¬-distribʳ-⊕ (par v) (par v))
  |  𝔽₂p.⊕-self (par v) | ℝp.ℝ\0^1 ∣ x ∣₀ =
  cong (_·_ (x ^ (v - 1ℤ))) $ ℝp.ℝ∪0∣x∣₀≡∣ℝ∪0x∣ x
```
:::

::: {.theorem #exponent-rules name="Exponent rules"}
Definition \@ref(def:real-powers) respects exponent rules, i.e. for $x,y\in\bR$
and $z,w\in\bZ_C$
\[x^{z+w}=x^z\cdot x^w;\quad (x\cdot y)^z=x^z\cdot y^z;\quad (x^z)^w = x^{zw}\]
:::
::: {.proof}
\
```agda
k-of-sum : (z w : ℤC) → par (val (z + w)) ⊕ par (z + w) ≡ let
  kz = par (val z) ⊕ par z; kw = par (val w) ⊕ par w in kz ⊕ kw
k-of-sum z w rewrite th-par-linearity-ℤ {val z} {val w}
   = 𝔽₂p.⊕-comm-middle (par (val z)) (par (val w)) (par z) (par w)

private
  sum-exp-helper : (x : ℝ\0) → (z w : ℤ) →
    x ^ ((z + w) + -[1+ 0 ]) · (∣ ℝ∪0 x ∣ · 1ℝ) ≡
      (x ^ (z + 0ℤ) · 1ℝ) · (x ^ (w + -[1+ 0 ]) · (∣ ℝ∪0 x ∣ · 1ℝ))
  sum-exp-helper x₀@(x≢0 x) z w rewrite ℤp.+-identityʳ z
    | ℝp.*-identityʳ (x₀ ^ z)
    | sym (ℝp.*-assoc (x₀ ^ z) (x₀ ^ (w + -[1+ 0 ])) (∣ x ∣ · 1ℝ))
    | ℤp.+-assoc z w -[1+ 0 ] =
    cong (_· (∣ x ∣ · 1ℝ)) (ℝp.sum-exp x₀ z (w + -[1+ 0 ]))

sum-exp : (x : ℝ\0) → (z w : ℤC) → x ^ (z + w) ≡ x ^ z · x ^ w
sum-exp x₀@(x≢0 x) z w rewrite k-of-sum z w with par (val z) ⊕ par z
  | par (val w) ⊕ par w
... | zero | zero rewrite ℤp.+-identityʳ (val z + val w) | ℤp.+-identityʳ (val z)
  | ℤp.+-identityʳ (val w) | ℝp.*-identityʳ (x₀ ^ (val z + val w))
  | ℝp.*-identityʳ (x₀ ^ val z) | ℝp.*-identityʳ (x₀ ^ val w)
  = ℝp.sum-exp x₀ (val z) (val w)
... | zero | one  = sum-exp-helper x₀ (val z) (val w)
... | one  | zero rewrite ℤp.+-comm (val z) (val w)
  | ℝp.*-comm (x₀ ^ (val z + -[1+ 0 ]) · (∣ x ∣ · 1ℝ)) (x₀ ^ (val w + 0ℤ) · 1ℝ) =
  sum-exp-helper x₀ (val w) (val z)
... | one  | one  rewrite ℝp.*-identityʳ ∣ x ∣
  | ℝp.*-comm-middle (x₀ ^ (val z + -[1+ 0 ])) (∣ x ∣)
                     (x₀ ^ (val w + -[1+ 0 ])) (∣ x ∣)
  | ℝp.∣x∣∣x∣ x | sym $ ℝp.sum-exp x₀ (val z + -[1+ 0 ]) (val w + -[1+ 0 ])
  | ℤp.+-comm-middle (val z) -[1+ 0 ] (val w) -[1+ 0 ]
  | ℝp.*-identityʳ (x₀ ^ ((val z + val w) + 0ℤ)) = sym $ trans
    (sym $ ℝp.sum-exp x₀ ((val z + val w) + -[1+ 1 ]) 2ℤ)
    (cong (_^_ x₀) $ ℤp.+-assoc (val z + val w) -[1+ 1 ] 2ℤ)

mul-base : (x y : ℝ\0) → (z : ℤC) → (x · y) ^ z ≡ x ^ z · y ^ z
mul-base x₀@(x≢0 x) y₀@(x≢0 y) z with par (val z) ⊕ par z
... | zero rewrite ℤp.+-identityʳ (val z) | ℝp.*-identityʳ (x₀ ^ val z)
  | ℝp.*-identityʳ (y₀ ^ val z) | ℝp.*-identityʳ ((x₀ · y₀) ^ val z) =
    ℝp.mul-base x₀ y₀ (val z)
... | one  rewrite ℝp.*-identityʳ ∣ x ∣ | ℝp.*-identityʳ ∣ y ∣
  | ℝp.*-identityʳ ∣ x · y ∣ | ℝp.*-comm-middle (x₀ ^ (val z - 1ℤ)) (∣ x ∣)
  (y₀ ^ (val z - 1ℤ)) ∣ y ∣ | ℝp.∣x∣∣y∣ x y = cong (_· ∣ x · y ∣) $
    ℝp.mul-base x₀ y₀ (val z - 1ℤ)

-- double-exp : (x : ℝ) → (z w : ℤC) → (x ^ z) ^ w ≡ x ^ (z · w)
-- double-exp x z w = {!   !}
```
:::

