/- Adapted by David Swinarski from files originally created by Heather Macbeth.  Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/

import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 2

Remember to look at the pdf file for Homework 2 in Blackboard for extra instructions. -/


@[autograded 4]
theorem problem1 {x : ℚ} (h1 : x ^ 2 = 9) (h2 : 1 < x) : x = 3 := by
  have imploding : x*(x+3) = 3*(x+3) := by
    calc
      x*(x+3) = x^2 + 3*x := by ring
      _ = 9 + 3*x := by rw[h1]
      _ = 3*(x+3) := by ring
  cancel x+3 at imploding

@[autograded 5]
theorem problem2 {s : ℚ} (h1 : 3 * s ≤ -15) (h2 : 2 * s ≥ -10) : s = -5 := by
  apply le_antisymm
  have LEBRON_JAMES : s <= -5 := by
    calc
      s = 3*s/3 := by ring
      _ <= -15/3 := by rel[h1]
      _ <= -5 := by numbers
  apply LEBRON_JAMES
  have KYRIE : s >= -5 := by
    calc
      s = 2*s/2 := by ring
      _ >= -10/2 := by rel[h2]
      _ >= -5 := by numbers
  apply KYRIE

@[autograded 2]
theorem problem3 {a b : ℝ} (h : a = 5 - b) : a + b = 2 ∨ a + b = 5 := by
  right
  addarith [h]


@[autograded 4]
theorem problem4 {t : ℚ} (h : t = -3 ∨ t = 2) : t ^ 2 + t - 6 = 0 := by
  obtain b | g := h
  · calc
    t^2 + t - 6 = t*t + t - 6 := by ring
    _ = -3*-3 + -3 - 6 := by rw[b]
    _ = 0 := by numbers
  · calc
    t^2 + t - 6 = t*t + t - 6 := by ring
    _ = 2*2 + 2 - 6 := by rw[g]
    _ = 0 := by numbers

@[autograded 5]
theorem problem5 {x : ℤ} : 2 * x ≠ 9 := by
  have h := le_or_succ_le x 4
  obtain b | g := h
  apply ne_of_lt
  · calc
      2*x <= 2*4 := by rel[b]
      _ = 8 := by numbers
      _ < 9 := by numbers
  apply ne_of_gt
  · calc
    2*x >= 2*5 := by rel[g]
    _ = 10 := by numbers
    _ > 9 := by numbers


@[autograded 5]
theorem problem6 {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 :=
    calc
      t^2*(t-1) = t^3 - t^2 := by ring
      _ = t^2 - t^2 := by rw[ht]
      _ = 0 := by ring
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain l | r := h2
  right
  apply pow_eq_zero l
  left
  addarith [r]

@[autograded 4]
theorem problem7 : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  numbers
  numbers

@[autograded 5]
theorem problem8 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1
  calc
    (x+1)^2 = x^2 + 2*x + 1 := by ring
    _ = x + (x^2 + x + 1) := by ring
    _ = (x^2 + 2*(1/2)*x + 1/4 + 3/4) + x := by ring
    _ = (x + 1/2)^2 + 3/4 + x := by ring
    _ >= 3/4 + x := by extra
    _ > x := by extra
