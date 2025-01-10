import Mathlib

theorem a_even_if_a_squared_even (a : ℤ) (h : Even (a^2)) : Even a := by
  -- Proof by contradiction
  by_contra h_not_even

  -- Convert "not even" to "odd"
  have h_odd : Odd a := by
    apply Int.odd_iff_not_even.mpr
    exact h_not_even

  -- Get representation of a as 2n + 1
  have ⟨n, h_rep⟩ : ∃ n : ℤ, a = 2 * n + 1 := by
    exact h_odd

  -- Calculate a²
  have h_square : a^2 = 4 * n^2 + 4 * n + 1 := by
    rw [h_rep]
    ring

  -- Show a² must be odd
  have h_square_odd : Odd (a^2) := by
    use 2 * n^2 + 2 * n
    rw [h_square]
    ring

  -- Reach contradiction: a² cannot be both even and odd
  have h_contra : ¬(Even (a^2) ∧ Odd (a^2)) := by
    intro h
    rcases h with ⟨heven, hodd⟩
    have := Int.not_odd_iff_even.2 heven  -- This gives us ¬(Odd (a^2))
    contradiction

  exact h_contra ⟨h, h_square_odd⟩
