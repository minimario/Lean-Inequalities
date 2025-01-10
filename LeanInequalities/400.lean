import Mathlib

#check PNat.add_one_coe

theorem sum_first_n_odd_integers (n : ℕ+) :
    (∑ k in Finset.range n, (2*k + 1)) = n^2 := by
  induction n using PNat.recOn with
  | p1 =>
    simp
  | hp n hi =>
    have h1 : ↑(n + 1 : ℕ+) = (↑n : ℕ) + 1 := by simp
    rw [h1]
    rw [Finset.sum_range_succ]
    rw [hi]
    ring
