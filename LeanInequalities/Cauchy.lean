import Mathlib

theorem cauchy_2 (a b c d : ℝ) : (a*c + b*d) ^ 2 ≤ (a^2 + b^2) * (c^2 + d^2) := by
  convert_to (∑ x : Fin 2, ![a, b] x * (![c, d] x))^2 ≤ (∑ x : Fin 2, (![a, b] x)^2) * (∑ x : Fin 2, (![c, d] x)^2)
  · simp [Fin.sum_univ_two]
  · simp [Fin.sum_univ_two]
  apply Finset.sum_mul_sq_le_sq_mul_sq

theorem inequality_proof (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + 1) * (b + 1) ≥ (Real.sqrt (a * b) + 1)^2 := by
  -- Apply Cauchy-Schwarz inequality
  have h := cauchy_2 (Real.sqrt a) 1 (Real.sqrt b) 1

  -- Simplify the left side of Cauchy-Schwarz
  have h1 : (Real.sqrt a * Real.sqrt b + 1 * 1)^2 = (Real.sqrt (a * b) + 1)^2 := by
    congr
    rw [← Real.sqrt_mul ha b]
    -- We need to prove that a * b ≥ 0
    norm_num

  -- Simplify the right side of Cauchy-Schwarz
  have h2 : (Real.sqrt a^2 + 1^2) * (Real.sqrt b^2 + 1^2) = (a + 1) * (b + 1) := by
    rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
    ring

  -- Rewrite the inequality
  rw [h1, h2] at h

  -- Apply the inequality
  exact h.ge

theorem sqrt_5_squared : (√5) * (√5) = 5 := by
  rw [← sq]
  rw [Real.sq_sqrt]
  norm_num

-- theorem test (a : ℝ): (√5) * a * (√5) = 5 * a := by
--   rw [mul_comm]
--   rw [mul_comm]
--   rw [mul_assoc]



--   rw [mul_comm, ← mul_assoc, ← sq, Real.sq_sqrt]
--   norm_num




theorem test (a : ℝ) : 5 * a^2 = (√5 * a)^2 := by
  ring
  field_simp

theorem test3 (a : ℝ) (h : a ≥ 0): √5^2 >= 5 - a := by
  ring
  field_simp
  linarith

theorem test2 (x : ℝ) :  1 - x^2 / (1 + x^2) = 1 / (1 + x^2) := by
  field_simp



theorem thm (a b : ℝ) :
  (1 + 5 * a^2) * 9 ≥ (2 + 5*a)^2 := by
  have h1 : √5 * a * √5 = 5 * a := by
    rw [mul_comm, ← mul_assoc, ← sq, Real.sq_sqrt]
    norm_num

  convert_to (∑ i : Fin 2, (![1, √5 * a] i)^2) * (∑ i : Fin 2, (![2, √5] i)^2) ≥ (∑ i : Fin 2, ![1, √5 * a] i * (![2, √5] i))^2
  · simp [Fin.sum_univ_two]
    have h : 5 * a^2 = (√5 * a)^2 := by
      rw [sq, sq, mul_mul_mul_comm]
      conv =>
        · right
          rw [← sq]

      rw [Real.sq_sqrt]
      norm_num
    rw [h]
    congr
    norm_num
  · simp [Fin.sum_univ_two]
    rw [h1]

  apply Finset.sum_mul_sq_le_sq_mul_sq

theorem thm' (x y : ℝ) (h : x = y) :
  -x = -y := by
  exact congrArg Neg.neg h

theorem thm2 (x : ℝ) (h : x^2 / (1+x^2) = 2) :
  1/(1+x^2)=-1 := by

  have h1 : 1 - x^2 / (1 + x^2) = 1 - 2 := by
    congr

  have h2 : 1 - x^2 / (1 + x^2) = 1 / (1 + x^2) := by
    have h3 : 1 = (1 + x^2) / (1 + x^2) := by
      rw [div_self]
      have h4 : 1 + x^2 > 0 := by
        apply add_pos_of_pos_of_nonneg
        · norm_num
        · exact sq_nonneg x
      apply ne_of_gt
      exact h4

    conv =>
      lhs
      lhs
      rw [h3]

    rw [← sub_div]
    congr
    ring

  rw [← h2]
  rw [h1]
  norm_num

theorem thm2' (x : ℝ) (h : x^2 / (1+x^2) = 2) :
  1/(1+x^2)=-1 := by

  
  at *
  linarith



    

  -- -- exfalso
  -- have h₀: x^2 ≤ (1 + x^2) := by linarith
  -- have h₁: 0 ≤ 1 + x^2 := by positivity
  -- have h₂: x^2 / (1 + x^2) ≤ 1 := div_le_one_of_le₀ h₀ h₁
  -- aesop
