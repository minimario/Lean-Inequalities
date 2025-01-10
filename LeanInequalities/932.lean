import Mathlib

theorem n_squared_plus_n_divisible_by_two (n : ℤ) : 2 ∣ (n^2 + n) := by
  -- First express n² + n as n(n+1)
  have h1 : n^2 + n = n * (n + 1) := by
    ring

  -- Now we consider two cases: n is even or odd
  have h2 : ∃ k : ℤ, (n = 2*k) ∨ (n = 2*k + 1) := by
    exact Int.exists_eq_two_mul_add_zero_or_one n

  -- From h2, we can do case analysis
  rcases h2 with ⟨k, h2⟩
  cases h2 with
  | inl h_even =>
    -- Case where n is even
    have h3 : 2 ∣ n := by
      use k
      exact h_even
    -- Therefore 2 divides the product
    rw [h1]
    exact dvd_mul_right 2 (n + 1)
  | inr h_odd =>
    -- Case where n is odd
    have h4 : 2 ∣ (n + 1) := by
      use k + 1
      rw [h_odd]
      ring
    -- Therefore 2 divides the product
    rw [h1]
    exact dvd_mul_left 2 n
