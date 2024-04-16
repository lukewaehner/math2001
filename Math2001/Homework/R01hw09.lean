/- Adapted by David Swinarski from files originally created by Heather Macbeth. Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Mathlib.Data.Real.Basic
import Library.Tactic.ModEq
import AutograderLib


/-! # Homework 9

Don't forget to compare with the pdf version
for clearer statements and any special instructions.
-/


-- Do 1a or 1b, but not both
-- Comment out or delete the unused portion
@[autograded 4]
theorem problem1a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  dsimp [Set.subset_def]
  intro x hx
  calc
    x ^ 3 - 7 * x ^ 2 = x*x^2 - 7*x^2 := by ring
    _ >= 10*x^2 - 7*x^2 := by rel[hx]
    _ = 3*x^2 := by ring
    _ = 3*x*x := by ring
    _ >= 3*10*x := by rel[hx]
    _ = 30*x := by ring
    _ = 26*x + 4*x := by ring
    _ >= 4*x := by extra


-- @[autograded 4]
-- theorem problem1b : { m : ℤ | m ≥ 10 } ⊈ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
--   sorry


-- Do 2a or 2b, but not both
-- Comment out or delete the unused portion
-- @[autograded 4]
-- theorem problem2a : { t : ℝ | t ^ 2 - 5 * t + 4 = 0 } = { s : ℝ | s = 4 } := by
--   sorry

@[autograded 4]
theorem problem2b : { t : ℝ | t ^ 2 - 5 * t + 4 = 0 } ≠ { s : ℝ | s = 4 } := by
  ext
  dsimp
  push_neg
  use 1
  left
  constructor
  ring
  numbers



-- Do 3a or 3b, but not both
-- Comment out or delete the unused portion
-- @[autograded 4]
-- theorem problem3a : {1, 2, 3} = {1, 2} := by
--   sorry



@[autograded 4]
theorem problem3b : {1, 2, 3} ≠ {1, 2} := by
  ext
  dsimp [Set.subset_def]
  push_neg
  use 3
  left
  constructor
  right
  right
  numbers
  constructor
  numbers
  numbers

@[autograded 4]
theorem problem4 : { r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ { s : ℤ | s ≡ 1 [ZMOD 2] } ∩ { t : ℤ | t ≡ 2 [ZMOD 5] } := by
  dsimp [Set.subset_def]
  intro n hn
  constructor
  dsimp [Int.ModEq] at *
  dsimp [(· ∣ ·)] at *
  obtain ⟨ x, hx ⟩ := hn
  have he : n - 1 = 10*x + 6 := by addarith[hx]
  use (5*x + 3)
  calc
    n - 1 = 10*x + 6 := he
    _ = 2*(5*x + 3) := by ring

  dsimp [Int.ModEq] at *
  dsimp [(· ∣ ·)] at *
  obtain ⟨ x, hx ⟩ := hn
  use (2*x + 1)
  calc
    n - 2 = 10*x + 5 := by addarith[hx]
    _ = 5*(2*x + 1) := by ring



variable {X : Type*}
variable (A B C : Set X)
open Set

@[autograded 4]
theorem problem5 (h : A ⊆ B) : A ∩ C ⊆ B ∩ C := by
  dsimp [Set.subset_def]
  intro x hx
  sorry
