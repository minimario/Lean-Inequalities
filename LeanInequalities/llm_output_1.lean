
import Mathlib

theorem divisibility_by_343 (x y z : ℕ) (h : x > 0 ∧ y > 0 ∧ z > 0)
  (h7 : 7 ∣ (x + 6*y) * (2*x + 5*y) * (3*x + 4*y)) :
  343 ∣ (x + 6*y) * (2*x + 5*y) * (3*x + 4*y) := by
  -- First show that x ≡ y (mod 7)
  have h1 : (x + 6*y) ≡ x - y (mod 7) := by
    apply Nat.ModEq.symm
    calc x - y
      ≡ x + 6*y (mod 7) := by
      rw [Nat.mod_eq_mod_iff_mod_sub_eq_zero]
      ring_nf
      norm_num

  have h2 : (2*x + 5*y) ≡ 2*(x - y) (mod 7) := by
    apply Nat.ModEq.symm
    calc 2*(x - y)
      ≡ 2*x + 5*y (mod 7) := by
      rw [Nat.mod_eq_mod_iff_mod_sub_eq_zero]
      ring_nf
      norm_num

  have h3 : (3*x + 4*y) ≡ 3*(x - y) (mod 7) := by
    apply Nat.ModEq.symm
    calc 3*(x - y)
      ≡ 3*x + 4*y (mod 7) := by
      rw [Nat.mod_eq_mod_iff_mod_sub_eq_zero]
      ring_nf
      norm_num

  -- Since 7 divides the product, x ≡ y (mod 7)
  have h4 : x ≡ y (mod 7) := by
    have h_prod : (x - y) * (2*(x - y)) * (3*(x - y)) ≡ 0 (mod 7) := by
      apply Nat.ModEq.trans _ h7
      ring_nf
    -- If product ≡ 0 (mod 7), then x - y ≡ 0 (mod 7)
    apply Nat.ModEq.symm
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.dvd_of_mod_eq_zero h_prod

  -- Now show each factor is divisible by 7
  have h5 : 7 ∣ (x + 6*y) := by
    apply Nat.dvd_of_mod_eq_zero
    have : x + 6*y ≡ 7*y (mod 7) := by
      rw [Nat.mod_eq_mod_iff_mod_sub_eq_zero]
      ring_nf
      exact h4
    exact this

  have h6 : 7 ∣ (2*x + 5*y) := by
    apply Nat.dvd_of_mod_eq_zero
    have : 2*x + 5*y ≡ 7*y (mod 7) := by
      rw [Nat.mod_eq_mod_iff_mod_sub_eq_zero]
      ring_nf
      exact h4
    exact this

  have h7' : 7 ∣ (3*x + 4*y) := by
    apply Nat.dvd_of_mod_eq_zero
    have : 3*x + 4*y ≡ 7*y (mod 7) := by
      rw [Nat.mod_eq_mod_iff_mod_sub_eq_zero]
      ring_nf
      exact h4
    exact this

  -- Therefore the product is divisible by 7³ = 343
  have h8 : 343 = 7^3 := by norm_num
  rw [h8]
  apply Nat.dvd_of_dvd_pow_three h5 h6 h7'
