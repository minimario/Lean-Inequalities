import Mathlib

open BigOperators
open Real


-- Problem 1:
-- Let $a_1$, $a_2$, $\cdots$, $a_n$, $b_1$, $b_2$, $\cdots$, $b_n$ be positive real numbers such that $a_1 + a_2 + \cdots + a_n = b_1 + b_2 + \cdots + b_n$. Show that
-- \[ \frac{a_1^2}{a_1 + b_1} + \frac{a_2^2}{a_2 + b_2} + \cdots + \frac{a_n^2}{a_n + b_n} \geq \frac{a_1 + a_2 + \cdots + a_n}{2} \]

-- Solution 1:

-- We multiply the two sides by $2(a_1+a_2+ \cdots a_n)$, the inequality is equivalent to
-- \[ 2(a_1+a_2 + \cdots +a_n)(\frac{a_1^2}{a_1 + b_1} + \frac{a_2^2}{a_2 + b_2} + \cdots + \frac{a_n^2}{a_n + b_n}) \geq (a_1 + a_2 + \cdots + a_n)^2  \]
-- Note that $a_1 + a_2 + \cdots + a_n = b_1 + b_2 + \cdots + b_n$, the LHS can be rewritten as
-- \[(a_1+a_2 + \cdots +a_n + b_1+a_2 + \cdots +b_n)(\frac{a_1^2}{a_1 + b_1} + \frac{a_2^2}{a_2 + b_2} + \cdots + \frac{a_n^2}{a_n + b_n}) \geq (a_1 + a_2 + \cdots + a_n)^2  \]
-- Finally, this can be put in the form
-- \[( (a_1+b_1) + (a_2+b_2) + \cdots (a_n+b_n))(\frac{a_1^2}{a_1 + b_1} + \frac{a_2^2}{a_2 + b_2} + \cdots + \frac{a_n^2}{a_n + b_n}) \geq (a_1 + a_2 + \cdots + a_n)^2  \]
-- which is exactly Cauchy-Schwarz inequality.

theorem inequality_p1 (n : ℕ) (a b : Fin n → ℝ)
    (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0)
    (sum_eq : ∑ i, a i = ∑ i, b i) :
    ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) / 2 := by sorry
