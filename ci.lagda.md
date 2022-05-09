# Complete integers

```agda
-- (c) Davide Peressoni 2022

open import Int
open import F2
```

## Complete integer numbers

::: {.definition name="Complete integers prime"}
Let's define the set of the complete integer numbers as

$$\mathbb{Z}_C' \coloneqq \mathbb{Z}\times\mathbb{F}_2$$

We will call the first component _value_, and the second _parity_.

```agda
record ℤC' : Set where
  constructor [_,_]
  field
    val : ℤ
    par : 𝔽₂
```
:::

::: {.definition name="Ring $\mathbb{Z}_C'$"}
Let's define $\mathbb{Z}_C'$ as a commutative ring with unit:

Given $[a,b], [c,d] \in \mathbb{Z}_C'$

$$[a,b] + [c,d] \coloneqq [a+c, b\oplus d]$$

```agda
instance
  open import Ops
  open Sum ⦃ ... ⦄ public
  SumℤC' : Sum ℤC'
  _+_ ⦃ SumℤC' ⦄ [ a , b ] [ c , d ] = [ a Int.+ c , b ⊕ d ]
```

$$[a,b] \cdot [c,d] \coloneqq [a\cdot c, b\cdot d]$$

```agda
instance
  open import Ops
  open Mul ⦃ ... ⦄ public
  MulℤC' : Mul ℤC'
  _·_ ⦃ MulℤC' ⦄ [ a , b ] [ c , d ] = [ a Int.· c , b F2.· d ]
```
:::

