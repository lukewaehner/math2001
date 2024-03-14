/- Adapted by David Swinarski from files originally created by Heather Macbeth. Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq


math2001_init

namespace Nat
open Int

-- Example 6.3.1
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n


example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  two_step_induction n with k IH1 IH2
  . calc
      a 0 = 2 := by rw [a]
      _ = 2 ^ 0 + (-1) ^ 0 := by numbers
  . calc
      a 1 = 1 := by rw [a]
      _ = 2 ^ 1 + (-1) ^ 1 := by numbers
  calc
    a (k + 2) = a (k + 1) + 2 * a k := by rw [a]
    _ = (2 ^ (k + 1) + (-1) ^ (k + 1)) + 2 * (2 ^ k + (-1) ^ k) := by rw [IH1, IH2]
    _ = (2 : ℤ) ^ (k + 2) + (-1) ^ (k + 2) := by ring


-- Example 6.3.1 again, using strong induction
theorem an_closed_formula (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  match n with
  | 0 =>
      calc
        a 0 = 2 := by rw [a]
        _ = 2 ^ 0 + (-1)^0 := by numbers
  | 1 =>
      calc
        a 1 = 1 := by rw [a]
        _ = 2 ^ 1 + (-1)^1:= by numbers
  | k+2  =>
      have IH1 := an_closed_formula k -- first inductive hypothesis
      have IH2 := an_closed_formula (k+1) -- second inductive hypothesis
      calc
        a (k + 2) = a (k + 1) + 2 * a k := by rw [a]
        _ = (2 ^ (k + 1) + (-1) ^ (k + 1)) + 2 * (2 ^ k + (-1) ^ k) := by rw [IH1, IH2]
        _ = (2 : ℤ) ^ (k + 2) + (-1) ^ (k + 2) := by ring
