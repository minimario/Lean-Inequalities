import Mathlib

theorem XAXAXA_divisible_by_7 (X A : ℕ) (hX : X < 10) (hA : A < 10) :
  ∃ k : ℕ, 101010 * X + 10101 * A = 7 * k := by
  -- Express the factorization of 10101
  have h1 : 10101 = 7 * 1443 := by
    norm_num

  -- Express XAXAXA in terms of XA × 10101
  have h2 : 101010 * X + 10101 * A = (10 * X + A) * 1443 * 7 := by
    ring

  -- Construct the witness k
  let k := (10 * X + A) * 1443

  -- Show this k satisfies our equation
  have h3 : 101010 * X + 10101 * A = 7 * k := by
    rw [h2]
    ring

  -- Conclude with existence of k
  exists k
