/- Adapted by David Swinarski from files originally created by Heather Macbeth. Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option quotPrecheck false

/-! # Homework 10

Don't forget to compare with the pdf version
for clearer statements and any special instructions.
-/

local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]


-- For each part a,b,c,d
-- prove one statement in Lean
-- then comment out or delete the unused portion
-- @[autograded 2]
-- theorem problem1a1 : Reflexive (· ∼ ·) := by
--   sorry

@[autograded 2]
theorem problem1a2 : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  numbers

-- @[autograded 2]
-- theorem problem1b1 : Symmetric (· ∼ ·) := by
--   sorry

@[autograded 2]
theorem problem1b2 : ¬ Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  push_neg
  use 1,2
  constructor
  numbers
  numbers

@[autograded 3]
theorem problem1c1 : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intro m n h1 h2
  have h3 :=
  calc
    m + n ≡ (n+1) + (m+1) [ZMOD 5] := by rel[h1,h2]
    _ = (m+n) + 2 := by ring
  obtain ⟨ k , hk ⟩ := h3
  have h4 :=
    calc
      5*k = m + n - (m+n+2) := by rw[hk]
      _ = -2 := by ring
  have h5 :=
    calc
      0 ≡ 0 + 5*(k+1) [ZMOD 5] := by extra
      _ = 5*k+ 5 := by ring
      _ = (-2) + 5 := by rw[h4]
      _ = 3 := by numbers
  numbers at h5


-- @[autograded 3]
-- theorem problem1c2 : ¬ AntiSymmetric (· ∼ ·) := by
--   sorry

@[autograded 2]
theorem problem1d2 : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, 3
  constructor
  numbers
  constructor
  numbers
  numbers


-- For each part a,b,c,d
-- prove one statement in Lean
-- then comment out or delete the unused portion
@[autograded 2]
theorem problem2a1 : Reflexive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Reflexive]
  intro x h1 h2
  apply h2

@[autograded 2]
theorem problem2b2 : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [Symmetric]
  push_neg
  use {1,2}, {1,2,3}
  constructor
  dsimp [Set.subset_def]
  intro a ha
  obtain h1 | h2 := ha
  left
  apply h1
  right
  left
  apply h2

  dsimp [Set.subset_def]
  push_neg
  use 3
  constructor
  right
  right
  numbers

  constructor
  numbers
  numbers

@[autograded 3]
theorem problem2c1 : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [AntiSymmetric]
  intro a b c d
  ext x
  constructor
  apply c
  apply d

-- @[autograded 3]
-- theorem problem2c2 : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
--   sorry

@[autograded 2]
theorem problem2d1 : Transitive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Transitive]
  intro a b c
  intro ha
  intro hb
  dsimp [Set.subset_def]
  intro x
  intro hx

  have h : x ∈ b
  apply ha hx
  apply hb h


-- @[autograded 2]
-- theorem problem2d2 : ¬ Transitive ((· : Set ℕ) ⊆ ·):= by
--   sorry
