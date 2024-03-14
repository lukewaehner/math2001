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
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


-- Induction Example 3 from my slides
-- Cf. also Example 6.2.4
example (n : ℕ) : 2*(Finset.sum (range (n + 1)) (fun i : ℕ ↦ i)) =  n * (n + 1) := by
  simple_induction n with k IH
  · rfl
  · calc
      2*(Finset.sum (range (k + 1 +1)) (fun i : ℕ ↦ i)) = 2*(Finset.sum (range (k + 1)) (fun i : ℕ ↦ i) +(k+1)) := by rw [Finset.sum_range_succ]
      _ = 2*(Finset.sum (range (k + 1)) (fun i : ℕ ↦ i)) +2*(k+1) := by ring
      _ = (k*(k+1)) + 2*(k+1) := by rw [IH]
      _ = (k+1)*(k+1+1) := by ring




-- Example 6.1.6
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2^(k+1) = 2 * 2^k := by ring
      _ ≥ 2*k^2 := by rel [IH]
      _ = k^2 + k*k := by ring
      _ ≥ k^2 + 4*k := by rel [hk]
      _ = k^2 + 2*k + 2*k := by ring
      _ ≥ k^2 + 2*k + 2*4 := by rel [hk]
      _ = (k+1)^2 + 7 := by ring
      _ ≥ (k+1)^2 := by extra





-- Recurrence relations
def a (n : ℕ) : ℕ := 2 ^ n

#eval a 20 -- infoview displays `1048576`

def b : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2*(b n)

#eval b 20

-- Example from slides
example (n : ℕ) : b n = 2^n := by
  simple_induction n with k IH
  calc
    b 0 = 1 := by rw[b]
    _ = 2^0 := by numbers
  calc
    b (k+1) = 2*(b k) := by rw[b]
    _ = 2*(2^k) := by rw[IH]
    _ = 2^(k+1) := by ring





-- Example 6.2.2

def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * x n - 1


example (n : ℕ) : x n ≡ 1 [ZMOD 4] := by
  simple_induction n with k IH
  calc
    x 0 = 5 := by rw[x]
    _ = 1+4*1 := by ring
    _ ≡ 1 [ZMOD 4] := by extra
  calc
    x (k+1) = 2*(x k) - 1 := by rw[x]
    _ ≡ 2*1 -1 [ZMOD 4]:= by rel [IH]
    _ = 1 := by ring
