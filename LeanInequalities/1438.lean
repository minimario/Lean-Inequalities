import Mathlib

theorem exists_power_minus_one_divisible (a n : ℕ) (h : Nat.Coprime a n) :
  ∃ m : ℕ, n ∣ (a^m - 1) := by
  -- We will use m = φ(n) as our witness
  use Nat.totient n

  -- State that we're using Euler's theorem
  have h1 : a^(Nat.totient n) ≡ 1 [MOD n] := by
    exact Nat.ModEq.pow_totient h

  -- Convert from modular arithmetic to divisibility
  have h2 : n ∣ (a^(Nat.totient n) - 1) := by
    rw [Nat.ModEq] at h1
    rw [Nat.dvd_iff_mod_eq_zero]
    exact Nat.sub_mod_eq_zero_of_mod_eq h1

  -- Our conclusion follows directly
  exact h2
