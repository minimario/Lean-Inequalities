
import Mathlib


lemma test (n m k c : ℕ) : n - (k+1)*c + 2*c = n - (k-1)*c := by
  -- Rewrite the left-hand side
  have h1 : n - (k+1)*c + 2*c = n - (k*c + c) + 2*c := by
    congr
    rw [Nat.mul_succ]

  -- Rearrange terms
  have h2 : n - (k*c + c) + 2*c = n - k*c - c + 2*c := by
    rw [Nat.sub_add_eq_sub_sub]

  -- Cancel out -c and 2*c
  have h3 : n - k*c - c + 2*c = n - k*c + c := by
    ring

  -- Rewrite the right-hand side
  have h4 : n - (k-1)*c = n - k*c + c := by
    rw [Nat.mul_sub_left_distrib]
    ring

  -- Combine all steps
  rw [h1, h2, h3, h4]

lemma divisibility_propagation (a : ℕ → ℕ+) (h : ∀ n m : ℕ, (a (n + 2*m)).val ∣ ((a n).val + (a (n + m)).val))
  (t n c : ℕ) (h1 : t ∣ (a n).val) (h2 : t ∣ (a (n - c)).val) :
  ∀ k : ℕ, t ∣ (a (n - k*c)).val := by
  intro k
  induction' k using Nat.strong_induction_on with k ih
  cases k with
  | zero =>
    simp
    exact h1
  | succ k =>
    have h_sum := h (n - (k+1)*c) c
    have h_eq : n - (k+1)*c + 2*c = n - (k-1)*c := by sorry
    have h_eq_2 : n-(k+1)*c+c = n - k*c := by sorry
    rw [h_eq, h_eq_2] at h_sum

    have h_div_k : t ∣ (a (n - k*c)).val := ih k (Nat.lt_succ_self k)
    have hhh : k - 1 < k + 1 := by
      exact Nat.sub_lt_succ k 1
    have h_div_km1 : t ∣ (a (n - (k-1)*c)).val := ih (k-1) hhh

    have h_sum_div_t : t ∣ ((a (n - (k+1)*c)).val + (a (n - k*c)).val) :=
      dvd_trans h_div_km1 h_sum

    have h_diff : t ∣ ((a (n - (k+1)*c)).val + (a (n - k*c)).val) - a (n - k * c) := by
      exact Nat.dvd_sub' h_sum_div_t h_div_k

    exact (Nat.dvd_add_iff_left h_div_k).mpr h_sum_div_t
