/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set



-- Example 9.1.3
example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  sorry


-- Example 9.1.4
example : {x : ℝ | 0 ≤ x ^ 2} ⊈ {t : ℝ | 0 ≤ t} := by
  sorry

-- Example 9.1.6
example : {a : ℕ | 4 ∣ a} ≠ {b : ℕ | 2 ∣ b} := by
  sorry

-- Example 9.1.7
example : {k : ℤ | 8 ∣ 5 * k} = {l : ℤ | 8 ∣ l} := by
  sorry


-- Example 9.1.8
example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := by
  sorry





-- Example 9.2.1
example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  sorry

/-
-- 9.2.2 first version
example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · sorry
    · sorry
  · sorry
-/
-- 9.2.2 second version
example : {2, 1} ∪ {2, 4} = {1, 2, 4} := by
  sorry

-- Adapted from Exercise 9.2.8 #6
example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} = {n : ℤ | 40 ∣ n} := by
  sorry
