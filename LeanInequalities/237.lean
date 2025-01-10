
import Mathlib

theorem divisibility_of_power_difference_1 (p : ℕ) (a b : ℤ) (hp : Nat.Prime p) (h : (p : ℤ) ∣ (a - b)) :
  (p : ℤ) ∣ (a^p - b) := by
  -- Convert divisibility to modular congruence
  have h1 : a ≡ b [ZMOD p] := by
    rw [Int.modEq_iff_dvd]
    have : b - a = -(a - b) := by ring
    rw [this]
    exact Int.dvd_neg.mpr h

  have h2 : a^p ≡ a [ZMOD p] := by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow]
    exact ZMod.pow_card (a : ZMod p)

  -- Use transitivity of modular congruence
  have h3 : a^p ≡ b [ZMOD p] := by
    apply Int.ModEq.trans h2
    exact h1

  -- Convert back to divisibility statement
  have h4 : (p : ℤ) ∣ (a^(p : ℕ) - b) := by
    rw [Int.modEq_iff_dvd] at h3
    have : b - a^(p : ℕ) = -(a^(p : ℕ) - b) := by ring
    rw [this] at h3
    exact Int.dvd_neg.mp h3

  exact h4

theorem divisibility_of_power_difference (p : ℕ+) (a b : ℤ) (hp : Nat.Prime p) (h : (p : ℤ) ∣ (a - b)) :
  (p : ℤ) ∣ (a^(p : ℕ) - b) := by
  -- Convert divisibility to modular congruence
  have h1 : a ≡ b [ZMOD p] := by
    rw [Int.modEq_iff_dvd]
    have : b - a = -(a - b) := by ring
    rw [this]
    exact Int.dvd_neg.mpr h

  have h2 : a^(p : ℕ) ≡ a [ZMOD p] := by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow]
    exact ZMod.pow_card (a : ZMod p)

  -- Use transitivity of modular congruence
  have h3 : a^(p : ℕ) ≡ b [ZMOD p] := by
    apply Int.ModEq.trans h2
    exact h1

  -- Convert back to divisibility statement
  have h4 : (p : ℤ) ∣ (a^(p : ℕ) - b) := by
    rw [Int.modEq_iff_dvd] at h3
    have : b - a^(p : ℕ) = -(a^(p : ℕ) - b) := by ring
    rw [this] at h3
    exact Int.dvd_neg.mp h3

  exact h4
