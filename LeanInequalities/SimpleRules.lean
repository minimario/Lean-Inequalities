import Mathlib

theorem p1 (a b : ℝ) (hab : a ≤ b) :
  a - b ≤ 0 := by
  exact tsub_nonpos.mpr hab

theorem p2 (a b k : ℝ) (hab : a ≤ b) (hk: k ≥ 0) :
  a ≤ b + k := by
  exact le_add_of_le_of_nonneg hab hk

theorem p3 (a b n : ℝ) (hab: a ≤ b) (ha : a ≥ 0) (hn : n ≥ 1) :
  a^n ≤ b^n := by
  apply Real.rpow_le_rpow
  · exact ha
  · exact hab
  · apply le_trans
    apply zero_le_one
    exact hn

theorem p4 (a b c : ℝ) (hb: b ≠ 0) (habc: a / b = c) :
  a = b * c := by
  have h1 : (a / b) * b = c * b := by rw [habc]
  have h2 : (a / b) * b = a := by
    exact div_mul_cancel₀ a hb
  rw [h2] at h1
  rw [mul_comm] at h1
  exact h1

theorem p5 (a b: ℕ) (ha : a % b = 0) : (k * a) % b = 0 := by
  rw [← Nat.mod_add_div a b]
  rw [ha]
  rw [zero_add]
  rw [← mul_assoc k b (a / b)]
  rw [mul_comm k b]
  rw [mul_assoc b k (a / b)]
  rw [Nat.mul_mod_right]

theorem p6 (a b c: ℝ) (hab : a = b) :
  a + c = b + c := by
  rw [hab]

theorem p7 (a b c: ℝ) (hab : a = b) :
  a * c = b * c := by
  rw [hab]

theorem p8 (a b c : ℝ) (h : a + b = c) : b = c - a := by
  rw [add_comm] at h
  exact eq_sub_of_add_eq h

theorem p9 (n : ℝ) (a : ℝ) (ha : a = 0) (hn: n > 0) :
  a^n = 0 := by
  refine (Real.rpow_eq_zero ?hx ?hy).mpr ha
  exact le_of_eq (id (Eq.symm ha))
  exact Ne.symm (ne_of_lt hn)

theorem p10 (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  rw [h₂]
  exact add_le_add_right h₁ d
