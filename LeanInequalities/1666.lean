import Mathlib

theorem even_not_div_by_4_not_sum_consecutive_odds :
  ∀ n m : ℕ,
  (2 ∣ n) ∧ ¬(4 ∣ n) →
  n ≠ (2*m + 1) + (2*m + 3) := by
  -- Start with arbitrary n, m
  intro n m h
  -- Prepare for contradiction
  intro heq
  -- Get the divisibility hypotheses
  have hdiv2 : 2 ∣ n := h.1
  have hndiv4 : ¬(4 ∣ n) := h.2

  -- Simplify the right side of the equation
  have hsum : (2*m + 1) + (2*m + 3) = 4*m + 4 := by
    ring

  -- Express as multiple of 4
  have hfactor : 4*m + 4 = 4*(m + 1) := by
    ring

  -- Combine our equations
  have h1 : n = 4*(m + 1) := by
    rw [heq, hsum, hfactor]

  -- This means n is divisible by 4
  have h2 : 4 ∣ n := by
    rw [h1]
    use (m + 1)

  -- Derive contradiction
  contradiction
