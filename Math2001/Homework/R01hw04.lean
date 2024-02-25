/- Adapted by David Swinarski from files originally created by Heather Macbeth.
Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Rel
import Library.Tactic.ModEq
import AutograderLib

math2001_init

namespace Int

open Int

/-! # Homework 4
  Remember to look at the pdf file for Homework 4
  in Blackboard for extra instructions.
-/


@[autograded 3]
theorem problem1 : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  use -1
  intro b
  use b
  calc
    -1 + b = b - 1 := by ring
    _ < b - 0 := by extra
    _ = b := by ring

@[autograded 4]
theorem problem2 : forall_sufficiently_large x : ℝ, x ^ 3 - 3 * x ≥ 6 * x ^ 2 := by
  dsimp
  use 7
  intro x hx

  calc
    x^3 - 3*x = x * x^2 - 3*x := by ring
    _ >= 7*x^2 - 3*x := by rel[hx]
    _ = 6*x^2 + x*x - 3*x := by ring
    _ >= 6*x^2 + 7*x - 3*x := by rel[hx]
    _ = 6*x^2 + 4*x := by ring
    _ >= 6*x^2 + 4*7 := by rel[hx]
    _ >= 6*x^2 := by extra


@[autograded 4]
theorem problem3 : ¬ (∃ t : ℝ, t ≤ 5 ∧ t ≥ 6) := by
  intro x
  obtain ⟨x , hx⟩ := x
  obtain ⟨ h1, h2 ⟩ := hx
  have h3 :=
    calc
      5 >= x := h1
      _ >= 6 := by rel [h2]
  numbers at h3

@[autograded 5]
theorem problem4 : ¬ (∃ a : ℝ, a ^ 2 ≤ 6 ∧ a ^ 3 ≥ 32) := by
  --apply abs_le_of_sq_le_sq'
  intro x
  obtain ⟨x , hx⟩ := x
  obtain ⟨ h1, h2 ⟩ := hx
  have test :=
    calc
      x^2 <= 6 := h1
      _ <= 9 := by numbers
      _ <= 3^2 := by numbers
  have h3 : -3 <= x ∧ x <= 3
  apply abs_le_of_sq_le_sq'
  apply test
  numbers

  have test2 :=
    calc
      x^3 = x*x^2 := by ring
      _ <= 3*x^2 := by rel[h3.2]
      _ <= 3*6 := by rel[h1]
      _ = 18 := by numbers
  have finalize :=
      calc
        32 <= x^3 := h2
        _ <= 18 := by rel[test2]
  numbers at finalize


@[autograded 5]
theorem problem5 (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
-- dsimp [Int.ModEq] at *
-- dsimp [(· ∣ ·)] at *
intro x
mod_cases hx: n % 4
· have h :=
    calc (0:ℤ) = 0^2 := by numbers
    _ ≡ n^2 [ZMOD 4] := by rel[hx]
    _ ≡ 2 [ZMOD 4] := by rel[x]

  numbers at h
· have h :=
      calc 1 = 1^2 := by numbers
      _ ≡ n^2 [ZMOD 4] := by rel [hx]
      _ ≡ 2 [ZMOD 4] := by rel[x]
  numbers at h
· have h :=
      calc 0 ≡ 0 + 4*1 [ZMOD 4] := by extra
      _ = 2^2 := by numbers
      _ ≡ n^2 [ZMOD 4] := by rel[hx]
      _ ≡ 2 [ZMOD 4] := by rel[x]
  numbers at h
· have h :=
      calc 1 ≡ 1 + 4*2 [ZMOD 4] := by extra
      _ = 3^2 := by numbers
      _ ≡ n^2 [ZMOD 4] := by rel[hx]
      _ ≡ 2 [ZMOD 4] := by rel[x]
  numbers at h



@[autograded 4]
theorem problem6 : Prime 113 := by
  apply better_prime_test (T := 11)
  · numbers
  · numbers
  intro x h1 h2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases x
  · use 56
    constructor <;> numbers
  · use 37
    constructor <;> numbers
  · use 28
    constructor <;> numbers
  · use 22
    constructor <;> numbers
  · use 18
    constructor <;> numbers
  · use 16
    constructor <;> numbers
  · use 14
    constructor <;> numbers
  · use 12
    constructor <;> numbers
  · use 11
    constructor <;> numbers

@[autograded 4]
theorem problem7 {x : ℝ} : x ^ 2 + 2 * x -15 = 0 ↔ (x = -5 ∨ x = 3) := by
  constructor
  · intro hx
    have h1 :=
      calc
        (x+5)*(x-3) = x ^ 2 + 2 * x -15 := by ring
        _ = 0 := by rw[hx]
    have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    obtain h2l | h2r := h2
    left
    addarith [h2l]
    right
    addarith [h2r]
  · intro hx
    obtain h1 | h2 := hx
    · calc
      x ^ 2 + 2 * x -15 = (-5)^2 + 2 * (-5) -15 := by rw[h1]
      _ = 0 := by numbers
    · calc
      x ^ 2 + 2 * x -15 = 3^2 + 2 * 3 -15 := by rw[h2]
      _ = 0 := by numbers


@[autograded 3]
theorem problem8 {x : ℤ} (hx : Int.Odd x) : Int.Odd (x ^ 3) := by
  rw [Int.odd_iff_modEq] at *
  calc
    x^3 ≡ 1^3 [ZMOD 2] := by rel[hx]
    _ = 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra
