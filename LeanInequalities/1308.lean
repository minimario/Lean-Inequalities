import Mathlib

theorem divisible_by_24 (n : ℤ) (h : n > 0) : 24 ∣ ((n + 7)^2 - (n - 5)^2) := by
  ring
  apply dvd_add
  · rfl
  · apply dvd_mul_left
