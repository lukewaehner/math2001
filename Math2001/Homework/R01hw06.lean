/- Adapted by David Swinarski from files originally created by Heather Macbeth. Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Mathlib.Algebra.BigOperators.Basic
import AutograderLib
open Finset



math2001_init
set_option pp.funBinderTypes true

/-! # Homework 6

Don't forget to compare with the pdf version
for clearer statements and any special instructions.

Question 5 does not have a required Lean component.-/

namespace Nat
open Int



@[autograded 4]
theorem problem1 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc
      (3:ℤ)^(k+1) = 2*(3^k) + 3^k := by ring
      _ >= 2*(2^k + 100) + 3^k := by rel[IH]
      _ = 2^(k+1) + 200 + 3^k := by ring
      _ = 2^(k+1) + 100 + (100 + 3^k) := by ring
      _ >= 2^(k+1) + 100 := by extra

/-
See the file In class demos/2024-03-11part1solutions.lean for an example similar to problem2 below.
-/
@[autograded 4]
theorem problem2 (n : ℕ) : 6*(Finset.sum (range (n + 1)) (fun i : ℕ ↦ i^2)) =  n * (n + 1)*(2*n+1) := by
  simple_induction n with k IH
  · rfl
  calc
    6*(Finset.sum (range (k + 1 +1)) (fun i : ℕ ↦ i^2)) = 6*(Finset.sum (range (k + 1)) (fun i : ℕ ↦ i^2) +(k+1)) := by rw [Finset.sum_range_succ]
     _ = 6*(Finset.sum (range (k + 1)) (fun i : ℕ ↦ i^2)) +6*(k+1) := by ring
     _ = (k * (k + 1) * (2 * k + 1)) + 6*(k+1) := by rw[IH]
     _ = (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) := by ring


--separate
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n


-- Do 3a with two step induction
@[autograded 4]
theorem problem3a (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · calc b 0 = 0 := by rw[b]
    _ = 1-1 := by ring
    _ = 3^0 - 2^0 := by numbers
  · calc b 1 = 1 := by rw[b]
    _ = 3^1 - 2^1 := by ring
  calc
    b (k + 2) = 5 * b (k+1) - 6*(b k) := by rw[b]
    _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 6*(b k) := by rw[IH2]
    _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 6*(3^k - 2^k) := by rw[IH1]
    _ = 5*3^(k+1)-6*3^k + 6*2^k - 5*2^(k+1) := by ring
    _ = 5*3^(k+1)-2*3*3^k + 3*2*2^k - 5*2^(k+1) := by ring
    _ = 5*3^(k+1)-2*3^(k+1) + 3*2^(k+1) - 5*2^(k+1) := by ring
    _ = 3^(k+1+1) - 2^(k+1+1) := by ring


-- Do 3b with strong induction
@[autograded 4]
theorem problem3b (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  match n with
  | 0 =>
    calc b 0 = 0 := by rw[b]
    _ = 3^0 - 2^0 := by numbers
  | 1 =>
    calc b 1 = 1 := by rw[b]
    _ = 3^1 - 2^1 := by numbers
  | k + 2 =>
    have IH1 := problem3b k
    have IH2 := problem3b (k+1)
    calc b (k + 2) = 5 * b (k+1) - 6*(b k) := by rw[b]
    _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 6*(b k) := by rw[IH2]
    _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 6*(3^k - 2^k) := by rw[IH1]
    _ = 5*3^(k+1)-6*3^k + 6*2^k - 5*2^(k+1) := by ring
    _ = 5*3^(k+1)-2*3*3^k + 3*2*2^k - 5*2^(k+1) := by ring
    _ = 5*3^(k+1)-2*3^(k+1) + 3*2^(k+1) - 5*2^(k+1) := by ring
    _ = 3^(k+1+1) - 2^(k+1+1) := by ring


/- Hints:
Apply the lemma even_or_odd n
In the even case, prove the additional hypotheses that 0 is less than k
and k is less than n
Then get an inductive hypothesis by calling problem4, as if we were doing
strong induction
-/
@[autograded 4]
theorem problem4 (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain h1 | h2 := Int.even_or_odd n
  obtain ⟨y, hy⟩ := h1
