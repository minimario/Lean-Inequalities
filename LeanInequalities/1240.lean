import Mathlib

theorem five_divides_square_iff_five_divides (a : ℤ) :
  5 ∣ a^2 ↔ 5 ∣ a := by
  constructor

  · intro h
    have five_prime : Nat.Prime 5 := by norm_num
    have five_prime_int : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr five_prime

    have h1 : a^2 = a * a := by exact pow_two a
    rw [h1] at h
    have h2 : 5 ∣ a ∨ 5 ∣ a := by
      exact five_prime_int.dvd_mul.mp h
    exact h2.elim id id

  · intro h
    rcases h with ⟨k, hk⟩
    have h1 : a^2 = (5*k)^2 := by
      rw [hk]
    have h2 : (5*k)^2 = 5*(5*k^2) := by
      rw [pow_two]
      ring
    rw [h1, h2]
    exact dvd_mul_right 5 (5*k^2)
