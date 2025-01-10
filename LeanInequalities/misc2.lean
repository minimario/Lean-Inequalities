import Mathlib

#print Prime.dvd_mul

theorem five_divides_square_iff_five_divides (a : ℤ) :
  5 ∣ a^2 ↔ 5 ∣ a := by
  constructor

  · intro h
    have five_prime : Prime 5 := by sorry
    have h1 : a^2 = a * a := by exact pow_two a
    rw [h1] at h
    have h2 : 5 ∣ a ∨ 5 ∣ a := by
      apply five_prime.dvd_mul h
    exact h2.elim id id
