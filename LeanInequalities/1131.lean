import Mathlib

theorem infinitely_many_primes_of_form_6k_plus_1 :
  ∀ n : ℕ, ∃ p : ℕ, p > n ∧ Prime p ∧ ∃ k : ℕ, p = 6 * k + 1 := by
  intro n
  -- Apply Dirichlet's theorem with q = 6 and a = 1
  have h := Nat.forall_exists_prime_gt_and_eq_mod (q := 6) (a := 1) (IsUnit.cast_one) n
  rcases h with ⟨p, p_gt_n, p_prime, p_mod_6⟩

  -- Now we have a prime p > n such that p ≡ 1 (mod 6)
  -- We need to show that this implies p = 6k + 1 for some k
  use p
  constructor
  · exact p_gt_n
  constructor
  · exact p_prime
  · -- Now we need to find k such that p = 6k + 1
    have h : ∃ k, p = 6 * k + 1 := by
      -- Use the division theorem
      have div_thm := Nat.div_mod_eq p 6
      rw [p_mod_6] at div_thm
      -- p = 6 * (p / 6) + 1
      use p / 6
      exact div_thm.symm
    exact h
