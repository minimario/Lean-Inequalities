import Mathlib
theorem lean_workbook_problem (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h_sum : a^2 + b^2 + c^2 = 3) :
  (Real.sqrt (b^2 + c^2) / (2 - a)) + (Real.sqrt (c^2 + a^2) / (2 - b)) ≤ 2 * (3 + 2 * Real.sqrt 6) / 5 := by sorry
