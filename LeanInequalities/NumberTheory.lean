import Mathlib

theorem no_prime_divisor_of_form_8k_minus_1 (n : ℕ+) :
  ∀ k : ℕ+, ∀ p : ℕ, Prime p → p = 8 * k - 1 → ¬(p ∣ ((2 : ℕ+)^n + 1)) :=
by sorry

theorem divisible_by_1957 (n : ℕ+) :
  ∃ k : ℤ, 1721^(2*n) - 73^(2*n) - 521^(2*n) + 212^(2*n) = 1957 * k := by sorry

-- theorem thm (n : ℕ) (h : n ≡ 0 [ZMOD 2]) :
--   (-1)^n = 1 := by
--   cases Nat.even_or_odd n with
--   | inl he =>
--     obtain ⟨k, hk⟩ := he
--     rw [hk]
--     simp [pow_mul]
--   | inr ho =>
--     exfalso
--     rw [Int.modEq_iff_dvd, zero_sub, dvd_neg] at h
--     norm_cast at h
--     apply Nat.not_even_iff_odd.mpr ho
--     exact (even_iff_exists_two_nsmul n).mpr h



-- theorem not_exists_prime_8_pow_plus_47 : ¬∃ n : ℕ, (8^n + 47).Prime := by
--   intro h
--   rcases h with ⟨n, hn⟩
--   -- have h1 : 8^n + 47 ≡ (-1)^n + 2 [ZMOD 3] := by
--   --   exact

--   have n_odd : Odd n := by
--     by_contra h_even
--     push_neg at h_even
--     apply Nat.not_odd_iff_even.mp at h_even
--     have : (8^n + 47) % 3 = 0 := by
--       apply Nat.mod_eq_of_modEq

--       norm_num
--       rw [this]
--       norm_num
--     have := Nat.dvd_of_mod_eq_zero this
--     exact Nat.Prime.not_dvd_one hn (Nat.dvd_trans ‹3 ∣ 8^n + 47› (Nat.dvd_add_right (Nat.dvd_pow_self 8 n) 47))

--   rcases n_odd with ⟨a, ha⟩
--   rw [ha] at hn

--   have h2 : 8^(2*a + 1) + 47 ≡ 3 [MOD 13] := by
--     have : 8^13 ≡ 1 [MOD 13] := by norm_num
--     have : 8^(2*a + 1) ≡ 8 [MOD 13] := by
--       rw [pow_add, pow_mul]
--       rw [Nat.ModEq.pow_congr this]
--       norm_num
--     rw [this]
--     norm_num

--   have h3 : 8^(2*a + 1) + 47 ≡ 0 [MOD 5] := by
--     have : 8^4 ≡ 1 [MOD 5] := by norm_num
--     have : 8^(2*a + 1) ≡ 8 [MOD 5] := by
--       rw [pow_add, pow_mul]
--       rw [Nat.ModEq.pow_congr this]
--       norm_num
--     rw [this]
--     norm_num

--   by_cases a_odd : Odd a
--   · have := Nat.dvd_of_mod_eq_zero (Nat.ModEq.symm h2).2
--     exact Nat.Prime.not_dvd_one hn (Nat.dvd_trans this (Nat.dvd_add_right (Nat.dvd_pow_self 8 (2*a + 1)) 47))
--   · push_neg at a_odd
--     have := Nat.dvd_of_mod_eq_zero (Nat.ModEq.symm h3).2
--     exact Nat.Prime.not_dvd_one hn (Nat.dvd_trans this (Nat.dvd_add_right (Nat.dvd_pow_self 8 (2*a + 1)) 47))
