
import Mathlib

theorem sum_consecutive_powers_of_two_divisible_by_six (n : ℕ) (h : n > 0) :
  ∃ k : ℤ, (2:ℤ)^n + (2:ℤ)^(n+1) = 6 * k := by
  -- Express 2^(n+1) in terms of 2^n
  have h1 : (2:ℤ)^(n+1) = 2 * (2:ℤ)^n := by
    rw [pow_succ]
    ring

  -- Rewrite the sum using this equality
  have h2 : (2:ℤ)^n + (2:ℤ)^(n+1) = (2:ℤ)^n + 2 * (2:ℤ)^n := by
    rw [h1]

  -- Factor out 2^n
  have h3 : (2:ℤ)^n + 2 * (2:ℤ)^n = (2:ℤ)^n * (1 + 2) := by
    ring

  -- Simplify to get 2^n * 3
  have h4 : (2:ℤ)^n * (1 + 2) = (2:ℤ)^n * 3 := by
    ring

  have h5 : (2:ℤ)^n * 3 = 2 * ((2:ℤ)^(n-1) * 3) := by
    rw [← mul_assoc]
    congr
    rw [← pow_succ']
    congr
    exact (Nat.sub_eq_iff_eq_add h).mp rfl

  let k := (2:ℤ)^(n-1)
  -- Show that the original expression equals 6 * k
  have h6 : (2:ℤ)^n + (2:ℤ)^(n+1) = 6 * k := by
    rw [h2, h3, h4, h5]
    ring_nf

  use k
