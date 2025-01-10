import Mathlib

open Finset

theorem inequality_proof (n : ℕ) (x y : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
  ∑ i, Real.sqrt (x i * y i) ≤ Real.sqrt (∑ i, x i) * Real.sqrt (∑ i, y i) := by
  have h1 : 0 ≤ ∑ i, Real.sqrt (x i * y i) := by
    apply sum_nonneg
    intro i
    exact Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (∑ i, x i) := by
    apply Real.sqrt_nonneg
    exact sum_nonneg (λ i => le_of_lt (hx i))
  have h3 : 0 ≤ Real.sqrt (∑ i, y i) := by
    apply Real.sqrt_nonneg
    exact sum_nonneg (λ i => le_of_lt (hy i))
  calc
    (∑ i, Real.sqrt (x i * y i))^2 ≤ (∑ i, x i) * (∑ i, y i) := by
      apply sum_sqrt_le_sqrt_sum_mul
      exact hx
      exact hy
    _ = (Real.sqrt (∑ i, x i) * Real.sqrt (∑ i, y i))^2 := by
      rw [← Real.sqrt_mul]
      · rw [Real.sqr_sqrt]
        · rfl
        · exact mul_nonneg (sum_nonneg (λ i => le_of_lt (hx i))) (sum_nonneg (λ i => le_of_lt (hy i)))
      · exact sum_nonneg (λ i => le_of_lt (hx i))
      · exact sum_nonneg (λ i => le_of_lt (hy i))
  exact Real.le_of_sqr_le_sqr h1 (mul_nonneg h2 h3) this


lemma sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι → ℝ≥0) :
    ∑ i ∈ s, f i * g i ≤ sqrt (∑ i ∈ s, f i ^ 2) * sqrt (∑ i ∈ s, g i ^ 2) :=
  (le_sqrt_iff_sq_le.2 <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq <| sqrt_mul _ _

theorem sum_square_le_sum_squares_times_three (a b c : ℝ≥0) :
    (a + b + c)^2 ≤ (a^2 + b^2 + c^2) * 3 := by
  -- Define our index type and finite set
  let ι := Fin 3
  let s : Finset ι := univ

  -- Define our functions
  let f : ι → ℝ≥0 := fun i => match i with
    | 0 => a
    | 1 => b
    | 2 => c

  let g : ι → ℝ≥0 := fun _ => 1

  -- Apply the lemma
  have h := sum_mul_le_sqrt_mul_sqrt s f g

  -- Simplify the left side of the inequality
  have left_side : ∑ i in s, f i * g i = a + b + c := by
    simp [f, g]
    ring

  -- Simplify the right side of the inequality
  have right_side : sqrt (∑ i in s, f i ^ 2) * sqrt (∑ i in s, g i ^ 2) =
      sqrt (a^2 + b^2 + c^2) * sqrt 3 := by
    simp [f, g]
    ring

  -- Rewrite the inequality using our simplifications
  rw [left_side, right_side] at h

  -- Square both sides (this is valid because both sides are non-negative)
  have h_squared := sq_le_sq.mpr h

  -- Simplify the squared inequality
  rw [sq_sqrt, sq_sqrt] at h_squared
  · exact h_squared
  · apply add_nonneg; apply pow_nonneg; exact zero_le a
  · apply mul_nonneg; exact zero_le_three; apply pow_nonneg; exact zero_le a



theorem inequality_proof (a b c x y z : ℝ)
--  (h1 : ∀ w ∈ {a, b, c, x, y, z}, -1 ≤ w ∧ w ≤ 1)
 (s1 : Set ℝ := {a, b, c, x, y, z})
--  (s2 : Set ℝ := {w | -1 ≤ w ∧ w ≤ 1})
 (h1: s1 ⊆ s2)
 (h2 : 1 + 2*a*b*c ≥ a^2 + b^2 + c^2)
 (h3 : 1 + 2*x*y*z ≥ x^2 + y^2 + z^2) :
 1 + 2*a*b*c*x*y*z ≥ a^2*x^2 + b^2*y^2 + c^2*z^2 := by sorry

def s1 : Set ℝ := {1, 2}
#check ℝ
#check ℕ
#check s1

#eval (5^(2005) % 7)
theorem equation_proof : (x + 1)^2 * x = x^3 + 2*x^2 + x := by ring

def my_set : Set ℕ := {1, 2, 3}

theorem lean_workbook_problem (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h_sum : a^2 + b^2 + c^2 = 3) :
  (Real.sqrt (b^2 + c^2) / (2 - a)) + (Real.sqrt (c^2 + a^2) / (2 - b)) ≤ 2 * (3 + 2 * Real.sqrt 6) / 5 := by sorry

#print Nat.Prime
#eval Nat.Prime 6

def primeDivisors (n : Nat) : List Nat :=
  List.filter (fun d => n % d == 0 && Nat.Prime d) (List.range (n + 1))

def smallestLargestPrimeDivisors (n : Nat) : Option (Nat × Nat) :=
  let divisors := primeDivisors n
  if divisors.isEmpty then
    none
  else
    some (divisors.head!, divisors.getLast!)

def sumSmallestLargestPrimeDivisors (n : Nat) : Option Nat :=
  match smallestLargestPrimeDivisors n with
  | none => none
  | some (smallest, largest) => some (smallest + largest)

#eval 15^4 + 16^4

#eval sumSmallestLargestPrimeDivisors 210

gg
