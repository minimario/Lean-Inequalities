import Mathlib

theorem divisible_by_seven_insertion (n : ℕ) (h : 7 ∣ n) :
  ∃ d : ℕ, d < 10 ∧ ∀ k : ℕ, 7 ∣ (n.div (10^k) * 10^(k+1) + d * (10^k - 1) + n.mod (10^k)) := by
  -- Let's find the appropriate digit d based on the remainder of n.div(10^k) mod 7
  let r := n.div (10^k) % 7
  -- We want d ≡ -3r (mod 7) and d < 10
  let d := (7 - (3 * r % 7)) % 7

  -- Show that our d is less than 10
  have h_d_lt_10 : d < 10 := by
    simp [d]
    apply Nat.mod_lt
    norm_num


  use d
  constructor
  · exact h_d_lt_10

  intro k

  -- Split the number into parts and work with congruences
  have h_cong : ∀ x y : ℕ, x ≡ y [MOD 7] → 7 ∣ (x - y) := by
    intro x y h_xy
    exact Nat.dvd_sub_of_mod_eq h_xy

  -- Show that 10 ≡ 3 (mod 7)
  have h_10_mod_7 : 10 % 7 = 3 := by norm_num

  -- Key congruence: 10r + d ≡ 0 (mod 7)
  have h_key : (10 * r + d) % 7 = 0 := by
    have h1 : 10 * r ≡ 3 * r [MOD 7] := by
      apply Nat.ModEq.mul_right
      rw [h_10_mod_7]
      exact Nat.mod_eq_of_lt (Nat.lt_succ_self 6)

    have h2 : d ≡ (7 - (3 * r % 7)) [MOD 7] := by
      apply Nat.mod_eq_of_lt
      exact Nat.lt_succ_self 6

    -- Combine congruences
    ring_nf
    norm_num

  -- Show that our construction maintains divisibility by 7
  have h_div : 7 ∣ (n.div (10^k) * 10^(k+1) + d * (10^k - 1) + n.mod (10^k)) := by
    -- Use the Chinese Remainder Theorem and congruences
    apply Nat.dvd_of_mod_eq_zero

    -- Work with modular arithmetic
    calc
      (n.div (10^k) * 10^(k+1) + d * (10^k - 1) + n.mod (10^k)) % 7
      ≡ (n.div (10^k) * 10 * 10^k + d * (10^k - 1) + n.mod (10^k)) [MOD 7] := by
        congr
        sorry
      ≡ ((10 * r + d) * 10^k + n.mod (10^k)) [MOD 7] := by
        ring_nf
        apply Nat.ModEq.symm
        apply Nat.ModEq.trans
        · apply Nat.ModEq.symm
          apply Nat.mod_eq_of_lt
          exact Nat.lt_succ_self 6
        · rfl
        sorry
      ≡ 0 [MOD 7] := by
        rw [h_key]
        ring
        exact h
        sorry

  exact h_div
