/- Adapted by David Swinarski from files originally created by Heather Macbeth. Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Mathlib.Algebra.BigOperators.Basic
open Finset

math2001_init

namespace Nat


-- Induction Example 6.1.1
example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  sorry


-- Induction Example 3 from my slides
-- Cf. also Example 6.2.4
example (n : ℕ) : Finset.sum (range (n + 1)) (fun i : ℕ ↦ 2*i) =  n * (n + 1) := by
  sorry


-- Example 6.1.6
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  sorry









-- Recurrence relations
def a (n : ℕ) : ℕ := 2 ^ n

#eval a 20 -- infoview displays `1048576`

def b : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2*(b n)

#eval b 20

-- Example from slides
example (n : ℕ) : b n = 2^n := by
  sorry




-- Example 6.2.2

def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * x n - 1


example (n : ℕ) : x n ≡ 1 [ZMOD 4] := by
  sorry
