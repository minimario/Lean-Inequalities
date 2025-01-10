import Mathlib

theorem prime_divides_prime_equal (p q : ℕ) (hp : Prime p) (hq : Prime q) (h : p ∣ q) : p = q := by
  -- A prime number cannot be 1
  have h1 : p ≠ 1 := by
    apply Prime.ne_one
    exact hp

  -- A prime only has 1 and itself as divisors
  have h2 : p = 1 ∨ p = q := by
    apply Or.inr
    rw [(Nat.Prime.dvd_iff_eq (Prime.nat_prime hq) h1).mp]
    exact h

  -- Therefore p must equal q
  cases h2 with
  | inl h_left => -- case p = 1
    contradiction
  | inr h_right => -- case p = q
    exact h_right
