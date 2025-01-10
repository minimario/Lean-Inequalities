import Mathlib

theorem sum_of_three_consecutive_cubes_divisible_by_9 (n : ℤ) :
  ∃ k : ℤ, n^3 + (n+1)^3 + (n+2)^3 = 9*k := by
  -- First express the expanded sum
  have h1 : (n+1)^3 = n^3 + 3*n^2 + 3*n + 1 := by
    ring

  have h2 : (n+2)^3 = n^3 + 6*n^2 + 12*n + 8 := by
    ring

  -- Combine the terms
  have h3 : n^3 + (n+1)^3 + (n+2)^3 = 3*n^3 + 9*n^2 + 15*n + 9 := by
    rw [h1, h2]
    ring

  -- Factor out 3
  have h4 : 3*n^3 + 9*n^2 + 15*n + 9 = 3*(n^3 + 3*n^2 + 5*n + 3) := by
    ring



  -- Let's define our quotient
  let k := n^3 + 3*n^2 + 5*n + 3

  -- Show that this k works
  have h5 : n^3 + (n+1)^3 + (n+2)^3 = 9*(k/3) := by
    rw [h3, h4]
    ring
    have h1 : 9 + n * 15 + n^2 * 9 + n^3 * 3 = 3 * 3 + n * (3 * 5) + n^2 * (3 * 3) + n^3 * 3 := by ring
    rw [h1]

    -- Factor out 3
    have h2 : 3 * 3 + n * (3 * 5) + n^2 * (3 * 3) + n^3 * 3 = 3 * (3 + n * 5 + n^2 * 3 + n^3) := by ring
    rw [h2]

    -- Apply the theorem
    rw [mul_div_mul_comm]
    · -- Simplify
      rw [Nat.div_one]
      rfl
    · -- Prove divisibility
      use 1
      ring
    · -- Prove divisibility
      use 3
      rfl



-- Conclude existence
exists k/3
