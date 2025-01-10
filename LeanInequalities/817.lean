import Mathlib

/-- Auxiliary lemma for difference of powers factorization -/
lemma diff_powers_factor (a b : ℕ) (n : ℕ) :
  ∃ k : ℕ, a^n - b^n = (a - b) * k := by
  induction n with
  | zero =>
    use 0
    simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    use a^n + k * b
    rw [Nat.pow_succ, Nat.pow_succ]
    sorry

theorem divisible_by_six (n : ℕ) : 6 ∣ (17^n - 11^n) := by
  -- First establish the difference of powers factorization
  have h1 : ∃ k : ℕ, 17^n - 11^n = (17 - 11) * k := by
    apply diff_powers_factor 17 11 n

  -- Extract the witness from the existential
  obtain ⟨k, hk⟩ := h1

  -- Show that 17 - 11 = 6
  have h2 : 17 - 11 = 6 := by
    norm_num

  -- Rewrite using this equality
  have h3 : 17^n - 11^n = 6 * k := by
    rw [hk, h2]

  -- Conclude divisibility
  have h4 : 6 ∣ (17^n - 11^n) := by
    rw [h3]
    exact dvd_mul_right 6 k

  exact h4
