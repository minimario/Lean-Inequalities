import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Sqrt

import Mathlib

import Mathlib.Analysis.InnerProductSpace.ProdL2

example (a b c d : ℝ) : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  linarith [show (a * d - b * c) ^ 2 ≥ 0 by positivity]

theorem cs_example (a b c d : ℝ) : (a*c + b*d)^2 ≤  (a^2+b^2)*(c^2+d^2) := by
  let u := ![a, b]
  let v := ![c, d]
  calc
    (a*c + b*d) ^ 2
    = ((u 0) * (v 0) + (u 1) * (v 1) ) ^ 2 := rfl
    _ = (∑ i, (u i) * (v i)) ^ 2 := by rw [Fin.sum_univ_two]
    _ ≤ (∑ i, (u i) ^ 2) * (∑ i, (v i) ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq ..
    _ = ((u 0) ^ 2 + (u 1) ^ 2 ) * ((v 0) ^ 2 + (v 1) ^ 2 )  := by repeat rw [Fin.sum_univ_two]
    _ = (a^2+b^2)*(c^2+d^2) := rfl

example (a b c d e f: ℝ) : (a*d + b*e + c*f) ^ 2 ≤ (a^2 + b^2 + c^2) * (d^2 + e^2 + f^2) := by
  let u := WithLp.equiv 2 _ |>.symm ![d, e, f]
  let v := WithLp.equiv 2 _ |>.symm ![a, b, c];
  have := norm_inner_le_norm (𝕜 := ℝ) v u
  apply sq_le_sq' (by trans 0; simp; positivity; positivity) at this
  simp [mul_pow, ← real_inner_self_eq_norm_sq, u, v,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, ← sq] at this
  exact this

theorem square_sum_product_ge_sum_product_square (a b c d e f : ℝ) :
    (a * d + b * e + c * f) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (d ^ 2 + e ^ 2 + f ^ 2) := by
  -- Define our index type and finite set
  let s := Finset.range 3

  -- Define our functions
  let f_1 : ℕ → ℝ := fun i => if i = 0 then a else (if i = 1 then b else c)
  let g_1 : ℕ → ℝ := fun i => if i = 0 then d else (if i = 1 then e else f)

  -- Apply Cauchy-Schwarz inequality
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f_1 g_1

  -- Simplify the left side of Cauchy-Schwarz
  have h_left : ∑ i in s, f_1 i * g_1 i = a * d + b * e + c * f := by
    simp only [mul_ite, ite_mul, s, f_1, g_1]
    rw [Finset.sum_range_succ_comm]
    simp
    rw [Finset.sum_range_succ_comm]
    simp
    ring

  have h_right_1 : ∑ i ∈ s, f_1 i ^ 2 = (a^2 + b^2 + c^2) := by
    simp only [mul_ite, ite_mul, s, f_1, g_1]
    rw [Finset.sum_range_succ_comm]
    simp
    rw [Finset.sum_range_succ_comm]
    simp
    ring

  have h_right_2 : ∑ i ∈ s, g_1 i ^ 2 = (d^2 + e^2 + f^2) := by
    simp only [mul_ite, ite_mul, s, f_1, g_1]
    rw [Finset.sum_range_succ_comm]
    simp
    rw [Finset.sum_range_succ_comm]
    simp
    ring

  rw [h_left, h_right_1, h_right_2] at h
  apply h

-- theorem square_sum_product_ge_sum_product_square (a b c d : ℝ) :
--     (a*c + b*d)^2 ≤ (a^2 + b^2) * (c^2 + d^2) := by
--   -- Define our index type and finite set
--   let ι := Fin 2
--   let s : Finset ι := Finset.univ

--   -- Define our functions
--   let f : ι → ℝ := fun i => if i = 0 then a else b
--   let g : ι → ℝ := fun i => if i = 0 then c else d

--   -- Apply Cauchy-Schwarz inequality
--   have h := Real.sum_mul_le_sqrt_mul_sqrt s f g

--   -- Simplify the left side of Cauchy-Schwarz
--   have h_left : ∑ i in s, f i * g i = a * c + b * d := by
--     simp only [mul_ite, ite_mul, s, f, g]
--     rw [Finset.sum_range_succ_comm]
--     simp only [one_ne_zero, ↓reduceIte, Finset.range_one, Finset.sum_singleton]
--     ring


--   -- Simplify the right side of Cauchy-Schwarz
--   have h_right : √(∑ i in s, f i ^ 2) * √(∑ i in s, g i ^ 2) = √(a^2 + b^2) * √(c^2 + d^2) := by
--     simp [f, g]
--     ring

--   -- Rewrite Cauchy-Schwarz with our simplifications
--   rw [h_left, h_right] at h

--   -- Square both sides (this is valid because both sides are non-negative)
--   have h_squared := sq_le_sq h

--   -- Simplify
--   rw [sq_mul, ← sq_sqrt (by positivity), ← sq_sqrt (by positivity)] at h_squared

--   -- The result follows
--   exact h_squared
