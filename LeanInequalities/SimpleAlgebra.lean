import Mathlib

theorem sqrt_plus_y_squared (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (Real.sqrt x + y + 1)^2 ≥ x + 2 * Real.sqrt x * y := by
  ring
  field_simp

  have h : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith

lemma difference_of_squares (x : ℝ): x^2 - 25 = (x - 5)*(x + 5) := by
  ring

lemma difference_of_squares_2 (x y : ℝ): x^2 - y^2 = (x - y)*(x + y) := by
  ring
