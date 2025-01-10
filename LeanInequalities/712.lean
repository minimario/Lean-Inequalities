import Mathlib

theorem pigeonhole_principle_divisibility_by_seven :
  ∀ (a : Fin 8 → ℤ), ∃ i j : Fin 8, i ≠ j ∧ (a i - a j) % 7 = 0 :=
by
  intro a

  have rem : Fin 8 → Fin 7 := λ i => ⟨(a i) % 7, by
    exact Int.mod_lt (a i) (by norm_num)⟩

  have h_exists : ∃ i j : Fin 8, i ≠ j ∧ rem i = rem j := by
    apply Fintype.exists_ne_map_eq_of_card_lt
    norm_num

  rcases h_exists with ⟨i, j, h_neq, h_rem⟩

  exists i, j
  constructor
  · exact h_neq
  · have h_mod : (a i) % 7 = (a j) % 7 := by
      sorry

    apply Nat.dvd_iff_mod_eq_zero.mpr
    suffices h : 7 ∣ (a i - a j) by exact h
    apply Nat.dvd_sub
    · exact Nat.mod_add_div' (a i) 7
    · exact Nat.mod_add_div' (a j) 7
    · exact h_mod
