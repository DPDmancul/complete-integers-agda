<!--
```agda
-- (c) Davide Peressoni 2022

{-# OPTIONS --safe #-}

open import Data.N
open import Data.Int
import Data.Integer.Properties as ℤp
open import Data.F2
import Data.F2.Properties as 𝔽₂p
open import Algebra
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Even
open import Data.Empty
open import Data.Product hiding(_×_)
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
  +-identityʳ z rewrite (+-comm z additive-zero) = +-identityˡ z

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
  ·-identityʳ z rewrite (·-comm z unit) = ·-identityˡ z

  ·-distribʳ-+ : (c a b : ℤC) → (a + b) · c ≡ a · c + b · c
  ·-distribʳ-+ [ vc , pc ] [ va , pa ] [ vb , pb ] =
    cong₂ [_,_] (ℤp.*-distribʳ-+ vc va vb) (𝔽₂p.∧-distribʳ-⊕ pc pa pb)
  ·-distribˡ-+ : (c a b : ℤC) → c · (a + b) ≡ c · a + c · b
  ·-distribˡ-+ c a b rewrite (·-comm c (a + b)) rewrite  (·-distribʳ-+ c a b)=
    (cong₂ _+_  (·-comm a c) (·-comm b c))

  ·-zeroˡ : (a : ℤC) → additive-zero · a ≡ additive-zero
  ·-zeroˡ [ v , p ] = cong₂ [_,_] (ℤp.*-zeroˡ v)  (𝔽₂p.∧-zeroˡ p)
  ·-zeroʳ : (a : ℤC) → a · additive-zero ≡ additive-zero
  ·-zeroʳ a rewrite (·-comm a additive-zero) = ·-zeroˡ a

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
lemma-ℤC-powers {z} {ℕ.suc n} = cong (_·_ z) (lemma-ℤC-powers {n = n})

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
  val x + val (n × x)          ≡⟨ cong (_+_ (val x))
                                  (th-val-homogeneityℕ-ℤC {x} {n}) ⟩
  val x + ℤ.pos n · val x      ≡⟨ cong (_+ ℤ.pos n · val x)
                                       (sym (ℤp.*-identityˡ (val  x))) ⟩
  1ℤ · val x + ℤ.pos n · val x ≡⟨ sym (ℤp.*-distribʳ-+ (val x) 1ℤ (ℤ.pos n)) ⟩
  (1ℤ + ℤ.pos n) · val x       ≡⟨⟩
  ℤ.pos (ℕ.suc n) · val x      ∎

th-val-homogeneity-ℤC : {x : ℤC} {z : ℤ} → val (z × x) ≡ z · val x
th-val-homogeneity-ℤC {z = ℤ.pos n}  = cong val (th-val-homogeneityℕ-ℤC {n = n})
th-val-homogeneity-ℤC {x} { -[1+ n ]} = begin
  val (-[1+ n ] × x)        ≡⟨⟩
  val (- (ℕ.suc n × x))     ≡⟨⟩
  - val (ℕ.suc n × x)       ≡⟨ cong (-_) (th-val-homogeneityℕ-ℤC {n = ℕ.suc n}) ⟩
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
... | even p | even q = parity-even (sum-even-even p q)
... | even p | odd  q = parity-odd  (sum-even-odd  p q)
... | odd  p | even q = parity-odd  (sum-odd-even  p q)
... | odd  p | odd  q = parity-even (sum-odd-odd   p q)


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
... | even p | even q = parity-even (mul-even-even p q)
... | even p | odd  q = parity-even (mul-even-odd  p q)
... | odd  p | even q = parity-even (mul-odd-even  p q)
... | odd  p | odd  q = parity-odd  (mul-odd-odd   p q)

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
  par z · par (z ^ ℕ.suc n) ≡⟨ cong (_·_ (par z)) (par-pow-ℤ {z} {n}) ⟩
  par z · par z             ≡⟨ 𝔽₂p.∧-idem (par z) ⟩
  par z                     ∎

par-pow-ℤC : {z : ℤC} {n : ℕ} → par (z ^ ℕ.suc n) ≡ par z
par-pow-ℤC {z} {0}       = 𝔽₂p.∧-identityʳ (par z)
par-pow-ℤC {z} {ℕ.suc n} = begin
  par (z ^ ℕ.suc (ℕ.suc n)) ≡⟨⟩
  par (z · z ^ ℕ.suc n)     ≡⟨ th-par-mul-ℤC {z} {z ^ ℕ.suc n} ⟩
  par z · par (z ^ ℕ.suc n) ≡⟨ cong (_·_ (par z)) (par-pow-ℤC {z} {n}) ⟩
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
ℤD = Σ[ ([ v , p ]) ∈ ℤC ] p ≡ par v → ⊥
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
    ℤ'-eq (cong [_, par v ] (lemma-sum-zero {ℤ}))

  Mulℤ' : Mul ℤ'
  _·_ ⦃ Mulℤ' ⦄ (a , refl) (b , refl) =
    a · b , sym (th-par-mul-ℤ {val a})
  unit       ⦃ Mulℤ' ⦄ = unit , refl
  lemma-unit ⦃ Mulℤ' ⦄ {[ v , _ ] , refl} =
    ℤ'-eq (cong [_, par v ] (lemma-unit {ℤ}))
```

```agda
module isomorphism-fℤ where

  ---------------------
  -- fℤ homomorphism --
  ---------------------

  addition : {a b : ℤ} → fℤ (a + b) ≡ fℤ a + fℤ b
  addition {a} {b} rewrite sym (th-par-linearity-ℤ {a} {b}) = refl

  multiplication : {a b : ℤ} → fℤ (a · b) ≡ fℤ a · fℤ b
  multiplication {a} {b} rewrite sym (th-par-mul-ℤ {a} {b}) = refl

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
won't write $\bZ'$ anymore and we will use the notation $[v, \Par(v)]$ to denote elements in $\bZ$ too.

More precisely we will write, with an abuse of notation, $\bZ'=\bZ$ and $[v,
\Par(v)] = v$ meaning respectively $\bZ'=f_{\bZ}(\bZ)$ and $[v, \Par(v)] =
f_{\bZ}(v)$.

## Behaviours induced by parity

We said in the introduction that dis-integers are the dual of integers along
parity, in fact in $\bZ_D$ we have $[0,1]$ which has null value and odd parity,
$[1,0]$ which has unitary value, but even parity, and in general $[v,p]$ where
the parity $p$ is not the parity of the integer $v$.

We now will show how this parity is not a mere binary flag, but induces the same
properties of even and odd numbers into $\bZ_C$: complete integers with even
parity act like even numbers and those with odd parity like odd numbers.

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
evenℤ→evenℤC : {z : ℤ} → Even z → ℤC-Even (proj₁ (fℤ z))
evenℤ→evenℤC p = even (parity-even p)

oddℤ→oddℤC : {z : ℤ} → Odd z → ℤC-Odd (proj₁ (fℤ z))
oddℤ→oddℤC p = odd (parity-odd p)

evenℤC→evenℤ : {z : ℤ'} → ℤC-Even (proj₁ z) → Even (fℤ⁻¹ z)
evenℤC→evenℤ {z} (even _) rewrite proj₂ z with even-or-odd (fℤ⁻¹ z)
... | even q = q

oddℤC→oddℤ : {z : ℤ'} → ℤC-Odd (proj₁ z) → Odd (fℤ⁻¹ z)
oddℤC→oddℤ {z} (odd _) rewrite proj₂ z with even-or-odd (fℤ⁻¹ z)
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

## Exponential of complete integers

Let's call $l \coloneqq [1,0]$ the even unit, since it has unitary value and
even parity.

```agda
l : ℤC
l = [ 1ℤ , zero ]
```

If we pick an $x \in \bR$ we can intuitively say that $x^l$ should be equal to
$|x|$ because:

1. being the parity of $l$ even, $x^l$ should be an even function of $x$;
2. being the value of $l$ one, $x^l$ should be a somewhat linear function of $x$.

We can now use this intuition to define

