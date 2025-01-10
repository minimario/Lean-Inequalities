import Mathlib

theorem n_minus_one_divides_n_squared_plus_n_minus_two (n : ℤ) (h_pos : n > 0) :
  (n - 1) ∣ (n^2 + n - 2) := by
  -- First handle the case where n = 0 separately

  -- Show the factorization identity
  have factorization : n^2 + n - 2 = (n - 1) * (n + 2) := by
    ring

  -- Use the factorization to prove divisibility
  have divides : (n - 1) ∣ ((n - 1) * (n + 2)) := by
    -- Show that any number divides its multiple
    apply dvd_mul_right

  -- Use the equality to conclude
  rw [←factorization] at divides
  exact divides
