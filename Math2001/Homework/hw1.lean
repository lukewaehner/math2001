/- Adapted by David Swinarski from files originally created by Heather Macbeth.  Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/

import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 1

Remember to look at the pdf file for Homework 1 in Blackboard for extra instructions. -/


@[autograded 5]
theorem problem1 {p q : ℤ} (h1 : p + 5 * q = 1) (h2 : q - 1 = 3) : p = -19 := by
  have h3 : q = 4 := by addarith[h2]
  calc
    p = p + 5*q - 5*q := by ring
    _ = 1 - 5*q := by rw[h1]
    _ = 1 - 5*4 := by rw[h3]

@[autograded 5]
theorem problem2 {a b : ℝ} (h1 : a + 2 * b = 10) (h2 : a - b = -2) : a = 2 := by
  have h3 : b = a + 2 := by addarith[h2]
  have h4 :=
    calc
      a + 2*b = a+2*(a+2) := by rw[h3]
      _ = 3*a + 4 := by ring
  have h5 :=
    calc
      3*a + 4 = a + 2*b := by rw[h4]
      _ = 10 := by rw[h1]
  have h6 : 3*a = 6 := by addarith[h5]
  have h7 :=
    calc a = 3*a/3 := by ring
    _ = 6/3 := by rw[h6]
    _ = 2 := by numbers
  apply h7



@[autograded 5]
theorem problem3 {x : ℤ} (hx : x ≥ 8) : x ^ 3 - 7 * x ^ 2 + 4 * x > 75 := by
  calc
    x^3 - 7*x^2 + 4*x = x* x^2 - 7*x^2 + 4*x := by ring
    _ >= 8*x^2 - 7*x^2 + 4*x := by rel[hx]
    _ = x^2 + 4*x := by ring
    _ = x*x + 4*x := by ring
    _ >= 8*x + 4*x := by rel[hx]
    _ = 12*x := by ring
    _ >= 12*8 := by rel[hx]
    _ = 96 := by numbers
    _ > 75 := by numbers
    --kill the powers to a int
@[autograded 5]
theorem problem4 {x : ℚ} : x ^ 2 - 4 * x ≥ -4 := by
  have h1 : x^2 - 4*x + 4 = (x-2)^2 := by ring
  have h2 : (x-2)^2 >= 0 := by extra
  calc
    x^2 - 4*x = x^2 - 4*x + 4 - 4 := by ring
    _ = (x-2)^2 - 4 := by rw[h1]
    _ >= 0 - 4 := by rel[h2]
    _ = -4 := by numbers
    -- complete the square


@[autograded 5]
theorem problem5 (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : a - b <= 0 := by addarith[h2]
  have needed : 0 <= a + b := by addarith[h1]
  have h4 :=
    calc
      a^2 - b^2 = (a-b)*(a+b) := by ring
      _ <= (0)*(a+b) := by rel[h3]
      _ = 0 := by ring
  have h5 : a^2 <= b^2 := by addarith[h4]
  apply h5
