/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7*k + 1

  calc
    7*n - 4 = 7*(2*k +1) - 4 := by rw[hk]
    _ = 14*k + 2 + 1 := by ring
    _ = 2*(7*k + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use (x*y + 2*y)

  calc
    x*y + 2*y = (2*a+1)*(2*b+1) + 2*(2*b+1) := by rw[ha,hb]
    _ = (2*b+1)*(2*a+1+2) := by ring
    _ = 2*(2*a*b + a + 3*b + 1) + 1 := by ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨t, ht⟩ := hm
  dsimp [Even]
  use (3*t - 1)
  calc
    3*m - 5 = 3*(2*t + 1) - 5 := by rw[ht]
    _ = 6*t + 3 - 5 := by ring
    _ = 2*(3*t - 1) := by ring



example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨t, ht⟩ := hn
  dsimp [Odd]
  use 2*t^2 + 2*t - 3
  calc
    n^2 + 2*n - 5 = (2*t)^2 + 2*(2*t) - 5 := by rw[ht]
    _ = 2*(2*t^2 + 2*t - 3) +1 := by ring


example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  dsimp [Odd]
  use -5
  numbers

example : Even (26 : ℤ) := by
  dsimp [Even]
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨t, ht⟩ := hm
  obtain ⟨l, hl⟩ := hn
  use (l+t)
  calc
    n + m = (2*l) + (2*t + 1) := by rw[hl,ht]
    _ = 2*(l+t)+1 := by ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨t, ht⟩ := hp
  obtain ⟨l, hl⟩ := hq
  use (t-l-2)
  calc
    p-q-4 = (2*t+1)-(2*l)-4 := by rw[ht,hl]
    _ = 2*(t-l-2) + 1 := by ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨t, ht⟩ := hb
  obtain ⟨l, hl⟩ := ha
  use (3*l + t - 1)
  calc
    3*a+b-3 = 3*(2*l) + (2*t+1) - 3 := by rw[ht,hl]
    _ = 2*(3*l + t - 1) := by ring


example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨t, ht⟩ := hr
  obtain ⟨l, hl⟩ := hs
  use (3*t - 5*l - 1)
  calc
    3*r - 5*s = 3*(2*t + 1) - 5*(2*l + 1 ) := by rw[ht,hl]
    _ =  2*(3*t - 5*l - 1) := by ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨t, ht⟩ := hx
  dsimp [Odd] at *
  calc
    x^3 = x*x*x := by ring
    _ = (2*t+1)*(2*t+1)*(2*t+1) := by rw[ht]
    _ = 8*t^3 + 8*t^2 + 3*t + 1:= by ring

--expand -> 2*(___) + 1

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  sorry

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  sorry

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  sorry

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  sorry

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  dsimp [Odd]
  use 1
  calc
    3*n^2 + 3*n -1 = 3*n*n + 3*n - 1 := by ring
    _ = 3*n*(n+1) - 1 := by ring
  --Case this out??

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  dsimp [Odd]
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  sorry
