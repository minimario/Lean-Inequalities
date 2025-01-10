import Mathlib

theorem divisibility_implication (a b c d : ℤ) (h : (a - c) ∣ (a * b + c * d)) :
  (a - c) ∣ (a * d + b * c) := by
  -- Let's consider the difference (ab + cd) - (ad + bc)
  have diff : (a * b + c * d) - (a * d + b * c) = (a - c) * (b - d) := by
    ring

  -- The difference is divisible by (a-c)
  have diff_dvd : (a - c) ∣ ((a * b + c * d) - (a * d + b * c)) := by
    rw [diff]
    exact dvd_mul_right (a - c) (b - d)

  -- From our hypothesis, ab + cd is divisible by (a-c)
  have h1 : (a - c) ∣ (a * b + c * d) := h

  -- Therefore, ad + bc must also be diviskoible by (a-c)
  have dvd_sub_imp : (a - c) ∣ (a * d + b * c) := by
    -- Use dvd_sub with h1 and diff_dvd, but rearrange the terms
    have : (a * b + c * d) - ((a * b + c * d) - (a * d + b * c)) = a * d + b * c := by ring
    rw [← this]
    exact dvd_sub h1 diff_dvd

  -- Conclude with the final result
  exact dvd_sub_imp
