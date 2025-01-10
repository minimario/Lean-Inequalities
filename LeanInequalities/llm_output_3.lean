import Mathlib

theorem three_digit_sum_divisible_by_37 (a b : ℕ) (ha : 100 ≤ a ∧ a < 1000) (hb : 100 ≤ b ∧ b < 1000)
  (hna : ¬(37 ∣ a)) (hnb : ¬(37 ∣ b)) (hs : 37 ∣ (a + b)) :
  37 ∣ (a * 1000 + b) := by
  -- First establish that 999 = 37 * 27
  have h999 : 999 = 37 * 27 := by
    norm_num

  -- Rewrite the target expression
  have h_rewrite : a * 1000 + b = 999 * a + (a + b) := by
    calc
      a * 1000 + b = (999 + 1) * a + b := by
        congr 1
        ring
      _ = 999 * a + a + b := by
        ring
      _ = 999 * a + (a + b) := by
        ring

  -- Show that 999 * a is divisible by 37
  have h_div_999a : 37 ∣ (999 * a) := by
    sorry

  -- Use the fact that both 999a and (a + b) are divisible by 37
  have h_div_sum : 37 ∣ (999 * a + (a + b)) := by
    apply dvd_add
    · exact h_div_999a
    · exact hs

  -- Conclude using our rewrite
  rw [←h_rewrite] at h_div_sum
  exact h_div_sum
