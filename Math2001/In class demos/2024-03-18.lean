/- Adapted by David Swinarski from files originally created by Heather Macbeth. Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int


def q (x : ℝ) : ℝ := 2*x + 5


#check @q -- infoview displays `q : ℝ → ℝ`


example : Injective q := by
  dsimp [Injective]
  intro x1 x2
  intro h
  calc
    x1 = (1/2)*( (2*x1 + 5)-5) := by ring
    _ = (1/2)*((q x1) - 5) := by rw[q]
    _ = (1/2)*((q x2) - 5) := by rw[h]
    _ = (1/2)*((2*x2+5)-5) := by rw[q]
    _ = x2 := by ring



example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -5, 5
  constructor
  numbers
  numbers

 example : Surjective q := by
  dsimp [Surjective]
  intro y
  use (y-5)/2
  calc
    q ((y-5)/2) = 2*((y-5)/2) + 5 := by rw[q]
    _ = y := by ring

example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -5
  intro x
  apply ne_of_gt
  calc
    -5 < 0 := by numbers
    _ ≤ x^2 := by extra


example : Bijective q := by
  dsimp [Bijective]




--def q (x : ℝ) : ℝ := 2*x + 5
def r (x : ℝ) : ℝ := x^2+1
def s (x : ℝ) : ℝ := 4*x^2+20*x+26



example : r ∘ q = s := by
  sorry




def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

#check @q -- infoview displays `q : ℝ → ℝ`

def t (x : ℝ) : ℝ := (x-5)/2


#check @t -- infoview displays `q : ℝ → ℝ`

example : Inverse q t := by
  dsimp[Inverse]
  constructor
  · ext x
    calc
      (t ∘  q) x = t (q x) := by rfl
      _ = t (2*x + 5 ) := by rw[q]
      _ = ((2*x+5)-5)/2 := by rw[t]
      _ = x := by ring
      _ = id x := by rw [id]
  · ext x
    calc
      (q ∘ t) x = q(t x) := by rfl
      _ = q ((x-5)/2) := by rw[t]
      _ = 2*((x-5)//2)+5 := by rw[q]
