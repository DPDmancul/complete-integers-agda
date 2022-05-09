
-- (c) Davide Peressoni 2022

---------------------
-- Integer numbers --
---------------------

module Int where
  open import Agda.Builtin.Int renaming (Int to ℤ) public
  open import Agda.Builtin.Nat renaming (_+_ to _+ℕ_; _-_ to _-ℕ_)
  open import Ops

  instance
    Sumℤ : Sum ℤ
    _+_ ⦃ Sumℤ ⦄ (pos a)           (pos b)          = pos (a +ℕ b)          -- a + b = a + b
    _+_ ⦃ Sumℤ ⦄ (negsuc a)        (negsuc b)       = negsuc (suc (a +ℕ b)) -- -(a + 1) + -(b + 1) = -((a + b + 1) + 1)
    _+_ ⦃ Sumℤ ⦄ (pos zero)        (negsuc b)       = negsuc b              -- 0 + -(b + 1) = -(b + 1)
    _+_ ⦃ Sumℤ ⦄ (pos (suc a))     (negsuc zero)    = pos a                 -- (a + 1) + -(0 + 1) = a
    _+_ ⦃ Sumℤ ⦄ (pos (suc a))     (negsuc (suc b)) = pos a + negsuc b      -- (a + 1) + -((b + 1) + 1) = a + -(b + 1)
    _+_ ⦃ Sumℤ ⦄ (negsuc a)        (pos zero)       = negsuc a              -- -(a + 1) + 0 = -(a + 1)
    _+_ ⦃ Sumℤ ⦄ (negsuc zero)     (pos (suc b))    = pos b                 -- -(0 + 1) + (b + 1) = b
    _+_ ⦃ Sumℤ ⦄ (negsuc (suc a)) (pos (suc b))     = negsuc a + pos b      -- -((a + 1) + 1) + (b + 1) = -(a + 1) + b

  instance
    Negateℤ : Sub ℤ
    -_ ⦃ Negateℤ ⦄ (pos zero)    = pos zero
    -_ ⦃ Negateℤ ⦄ (pos (suc a)) = negsuc a
    -_ ⦃ Negateℤ ⦄ (negsuc a)    = pos (suc a)

  instance
    Mulℤ : Mul ℤ
    _·_ ⦃ Mulℤ ⦄ (pos a)       (pos b)       = pos (a * b)                -- a · b = a · b
    _·_ ⦃ Mulℤ ⦄ (pos zero)    (negsuc b)    = pos zero                   -- 0 · -(b + 1) = 0
    _·_ ⦃ Mulℤ ⦄ (pos (suc a)) (negsuc b)    = negsuc (suc a * b +ℕ a)    -- (a + 1) · -(b + 1) = -((a + 1) · b + (a + 1)) = -(((a + 1) · b + a) + 1)
    _·_ ⦃ Mulℤ ⦄ (negsuc a)    (pos zero)    = pos zero                   -- -(b + 1) · 0 = 0
    _·_ ⦃ Mulℤ ⦄ (negsuc a)    (pos (suc b)) = negsuc (b * suc a +ℕ b)    -- -(a + 1) · (b + 1) = -(a · (b + 1) + (b + 1)) = -((a · (b + 1) + b) + 1)
    _·_ ⦃ Mulℤ ⦄ (negsuc a)    (negsuc b)    = pos (a * b +ℕ a +ℕ b +ℕ 1) -- -(a + 1) · -(b +1) = a · b + a + b + 1


