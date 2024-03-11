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
  sorry


-- Example 6.3.1 again, using strong induction
theorem an_closed_formula (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  sorry
