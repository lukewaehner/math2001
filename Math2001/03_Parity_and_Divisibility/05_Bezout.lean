/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨k, hk⟩ := hn
  use (5*k - 3*n)
  calc
    n = 25*n - 24*n := by ring
    _ = 5*(5*n) - 24*n := by ring
    _ = 5*(8*k) - 24*n := by rw[hk]
    _ = 8*(5*k - 3*n) := by ring

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  sorry

example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨j, hj⟩ := hn
  use (-j + 2*n)
  calc
    n =  -11*n + 12*n := by ring
    _ = -1*(11*n - 12*n) := by ring
    _ = -1*(6*j - 12*n) := by rw[hj]
    _ = -6*j + 12*n := by ring
    _ = -6*(j - 2*n) := by ring
    _ = 6*(-j + 2*n) := by ring


example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  sorry

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  sorry

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  sorry
