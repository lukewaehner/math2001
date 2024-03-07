/- Adapted by Kåre Schou Gjaldbæk from files originally created by Heather Macbeth.
Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init

namespace Int

open Int

/-! # Homework 3
  Remember to look at the pdf file for Homework 3
  in Blackboard for extra instructions.
-/


@[autograded 5]
theorem problem01 {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨k, hk⟩ := hx
  dsimp [Odd]
  use (4*k^3 + 6*k^2 + 3*k)
  calc
    x^3 = (x*x*x) := by ring
    _ = (2*k+1)*(2*k+1)*(2*k+1) := by rw[hk]
    _ = 8*k^3 + 12*k^2 + 6*k + 1 := by ring
    _ = 2*(4*k^3 + 6*k^2 + 3*k) + 1 := by ring


@[autograded 6]
theorem problem02 (n : ℤ) : Odd (3 * n ^ 2 + 7 * n + 9) := by
  obtain hk | hk := Int.even_or_odd n
  obtain ⟨t, ht⟩ := hk
  use (6*t^2 + 7*t + 4)
  calc
     3*n ^ 2 + 7*n + 9 = 3*(2*t)^2 + 7*(2*t) + 9 := by rw[ht]
     _ = 12*t^2 + 14*t + 9 := by ring
     _ = 2*(6*t^2 + 7*t + 4) + 1 := by ring
  obtain ⟨t, ht⟩ := hk
  use (6*t^2 + 13*t + 9)
  calc
    3*n^2 + 7*n + 9 = 3*(2*t + 1)^2 + 7*(2*t+1) + 9 := by rw[ht]
    _ = 12*t^2 + 26*t + 19 := by ring
    _ = 2*(6*t^2 + 13*t + 9) + 1 := by ring
    --test if n is even or odd

@[autograded 2]
theorem problem03 : (4 : ℤ) ∣ -20 := by
  dsimp [(· ∣ ·)]
  use -5
  numbers
    --4k = -20

@[autograded 3]
theorem problem04 : ¬(4 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -3
  constructor
  numbers
  numbers
    --4k = -10 ?? no int fits that.
    --Can be shown by 4(-3) < -10 && 4(-3+1) > -10

@[autograded 4]
theorem problem05 {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c := by
  dsimp [(· ∣ ·)] at *
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  use (x^3*y)
  calc
    c = b^3*y := by rw[hy]
    _ = (a^2*x)^3 * y := by rw[hx]
    _ = a^6*x^3 * y := by ring
    _ = a^6*(x^3*y) := by ring

    -- parse it all out and just manuever it through.
    -- It works eventually its just a substitution problem

@[autograded 4]
theorem problem06 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  dsimp [Int.ModEq] at *
  use (x+y)
  calc
    a-c = (a-b) + (b-c) := by ring
    _ = n*x + n*y := by rw[hx,hy]
    _ = n*(x+y) := by ring

@[autograded 4]
theorem problem07 {x : ℤ} (h : x ≡ 3 [ZMOD 5]) :
    (2 * x + 3) ^ 2 ≡ (2 * 3 + 3) ^ 2 [ZMOD 5] := by
  apply Int.ModEq.pow
  apply Int.ModEq.add
  apply Int.ModEq.mul
  extra
  rel[h]
  extra


@[autograded 4]
theorem problem08 {a : ℤ} (ha : a ≡ 4 [ZMOD 5]) :
    a ^ 3 + 4 * a ^ 2 + 3 ≡ 1 [ZMOD 5] :=
  calc
    a ^ 3 + 4 * a ^ 2 + 3 ≡ (4)^3 + 4*(4)^2 + 3 [ZMOD 5]:= by rel[ha]
    _ ≡ 64 + 64 + 3 [ZMOD 5] := by numbers
    _ = 1 + 5 * 26 := by numbers
    _ ≡ 1 [ZMOD 5] := by extra


@[autograded 4]
theorem problem09 : ∃ k : ℤ, 5 * k ≡ 4 [ZMOD 9] := by
  dsimp [Int.ModEq] at *
  dsimp [(· ∣ ·)] at *
  use -1
  use -1
  calc
    5 * -1 - 4 = -9 := by ring
    _ = 9 * -1 := by ring

@[autograded 5]
theorem problem10 {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  dsimp [Int.ModEq] at *
  dsimp [(· ∣ ·)] at *
  mod_cases hx: x % 5
  · calc
      x^5 ≡ 0^5 [ZMOD 5] := by rel [hx]
      _ = 0 := by numbers
      _ ≡ x [ZMOD 5] := by rel[hx]
  · calc
      x^5 ≡ 1^5 [ZMOD 5] := by rel[hx]
      _ = 1 := by numbers
      _ ≡ x [ZMOD 5] := by rel[hx]
  · calc
      x^5 ≡ 2^5 [ZMOD 5] := by rel[hx]
      _ = 2 + 5*6 := by numbers
      _ ≡ 2 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel[hx]
  · calc
      x^5 ≡ 3^5 [ZMOD 5] := by rel[hx]
      _ = 3 + 5*48 := by numbers
      _ ≡ 3 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel[hx]
  · calc
      x^5 ≡ 4^5 [ZMOD 5] := by rel[hx]
      _ = 4 + 5*204 := by numbers
      _ ≡ 4 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel[hx]

  -- mod residues
