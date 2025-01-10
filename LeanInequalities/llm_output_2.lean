import Mathlib

theorem prime_divides_square_implies_divides (p n : ℤ) (hp : Prime p) (h : p ∣ n^2) : p ∣ n := by
  -- Express n² as n × n
  have h1 : n^2 = n * n := by
    rw [pow_two]

  -- Rewrite the division condition using this equality
  have h2 : p ∣ (n * n) := by
    rw [h1] at h
    exact h

  -- Apply the prime divisibility property
  -- If p is prime and p∣(a×b), then p∣a or p∣b
  have h3 : p ∣ n ∨ p ∣ n := by
    exact Prime.dvd_mul_iff.mp hp h2

  -- Both cases lead to the same conclusion
  cases h3 with
  | inl h_left => exact h_left
  | inr h_right => exact h_right
