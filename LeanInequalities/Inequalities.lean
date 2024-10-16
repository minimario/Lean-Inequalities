import Mathlib

-- [Problem 1]
-- Let $a_1$, $a_2$, $\cdots$, $a_n$, $b_1$, $b_2$, $\cdots$, $b_n$ be positive real numbers such that $a_1 + a_2 + \cdots + a_n = b_1 + b_2 + \cdots + b_n$. Show that
-- \[ \frac{a_1^2}{a_1 + b_1} + \frac{a_2^2}{a_2 + b_2} + \cdots + \frac{a_n^2}{a_n + b_n} \geq \frac{a_1 + a_2 + \cdots + a_n}{2} \]

-- [Solution 1]
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


-- [Problem 2]
-- For positive reals $a,b,c$, we have
--     \[ \frac{a}{b+c} + \frac{b}{c+a} + \frac{c}{a+b} \geq \frac{3}{2}. \]

-- [Solution 2]
-- By adding $1$ on each term on the LHS, we the inequality is equivalent to
-- \[ (\frac{a}{b+c} + 1)  + (\frac{b}{c+a}+ 1)  + (\frac{c}{a+b}+ 1)  \geq \frac{3}{2}+ 3  \]
-- Expanding it gives
-- \[ \frac{a+b+c}{b+c} + \frac{b+c+a}{c+a} + \frac{c+a+b}{a+b} \geq \frac{9}{2}\]
-- Factorizing it gives
-- \[ (a+b+c) (\frac{1}{b+c} + \frac{1}{c+a} + \frac{1}{a+b} )\geq \frac{9}{2}\]
-- Multiply both sides by $2$ yields
-- \[ 2(a+b+c) (\frac{1}{b+c} + \frac{1}{c+a} + \frac{1}{a+b} )\geq 9 \]
-- It suffices to rewrite it as
-- \[ ((b+c) + (c+a) + (a+b)) (\frac{1}{b+c} + \frac{1}{c+a} + \frac{1}{a+b} )\geq (1+1+1)^2 \]
-- which is exactly Cauchy Schwartz.

theorem inequality_p2 (a b c : ℝ)
    (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by sorry


-- [Problem 3]
-- Let $x, y, z$ be real numbers greater than $1$ and such that $\frac{1}{x} + \frac{1}{y} + \frac{1}{z} = 2$.
-- Prove that \[ \sqrt{x + y + z} \ge \sqrt{x-1} + \sqrt{y-1} + \sqrt{z-1}. \]

-- [Solution 3]
-- By the Cauchy-Schwarz Inequality, we have \[ (x+y+z) \left(\frac{x-1}{x} + \frac{y-1}{y} + \frac{z-1}{z} \right) \ge (\sqrt{x-1} + \sqrt{y-1} + \sqrt{z-1})^2. \]
-- Note that $\frac{x-1}{x} + \frac{y-1}{y} + \frac{z-1}{z} = 3 - \frac{1}{x} - \frac{1}{y} - \frac{1}{z} = 1$
-- so this yields $\sqrt{x + y + z} \ge \sqrt{x-1} + \sqrt{y-1} + \sqrt{z-1}$

theorem inequality_p3 (x y z : ℝ)
    (hx : x > 1) (hy : y > 1) (hz : z > 1)
    (h : 1/x + 1/y + 1/z = 2) :
  Real.sqrt (x + y + z) ≥ Real.sqrt (x - 1) + Real.sqrt (y - 1) + Real.sqrt (z - 1) := by sorry


-- [Problem 4]
-- If $a, b, c \in (0, 1)$. Prove that \[ \sqrt{abc} + \sqrt{(1-a)(1-b)(1-c)} < 1. \]

-- [Solution 4]
-- By the Cauchy-Schwarz Inequality, we have \[ (1-a+a)(1-b+b) \ge \left(\sqrt{(1-a)(1-b)}+\sqrt{ab}\right)^2 > (1-a)(1-b) + ab \]
-- By Cauchy-Schwarz again, we have \[ 1 = (1-a+a)(1-b+b)(1-c+c) > ((1-a)(1-b)+ab)(1-c+c) \ge \sqrt{(1-a)(1-b)(1-c)} + \sqrt{abc} \]

theorem inequality_p4 (a b c : ℝ)
    (ha : 0 < a) (ha' : a < 1)
    (hb : 0 < b) (hb' : b < 1)
    (hc : 0 < c) (hc' : c < 1) :
  Real.sqrt (a * b * c) + Real.sqrt ((1 - a) * (1 - b) * (1 - c)) < 1 := by sorry
