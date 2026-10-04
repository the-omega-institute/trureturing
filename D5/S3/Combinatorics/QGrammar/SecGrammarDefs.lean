/- GID: D5/S3/Combinatorics/QGrammar/SecGrammarDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/QGrammar/SecGrammarDefs
   mirror-E: none(waiver:q-grammar-support-statement-definition)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Basic, mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Han, Ji and Xiong's conjectured number of distinct terms of the iterated q-derivative of y0 for the grammar GSec. -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.QGrammar.SecGrammarDefs

open Polynomial

/-! Fixed public statement: Han, Ji and Xiong, *q-Derivative Grammar*, arXiv:2604.23959v2, §3
    (Definitions 3.3–3.7) and Appendix III, Conjecture III.7.  The grammar `G_Sec` has the rules
    `x_j ↦ q^j (1 + x_j x_{j+1})` and `y_j ↦ q^j y_j x_{j+1}` and the order DIO, which sorts the
    variables of a word by descending index, `x` before `y` at equal index.  The q-derivative is
    `D(w₁⋯wₙ) = ∑_j DIO(w₁⋯w_{j-1} R(w_j) ↑(w_{j+1}⋯wₙ))`, where `↑` raises every index of the
    suffix by one, extended linearly to formal sums of words with coefficients in `ℤ[q]`.
    `Ω(E)` is the number of distinct words with nonzero coefficient in `E`.  Conjecture III.7:
    `Ω(Dⁿ(y₀)) = 1, 3, (20k³ + 33k² + k - 6)/6, (20k - 17)(k + 1)k/6` for `n = 1`, `n = 2`,
    `n = 2k + 1` with `k ≥ 1`, and `n = 2k` with `k ≥ 2`, respectively. -/

/-- A variable: `(false, j)` is `x_j` and `(true, j)` is `y_j`. -/
abbrev Var := Bool × ℕ

/-- The DIO precedence: higher index first, and `x` before `y` at equal index. -/
def dioLe (a b : Var) : Prop := b.2 < a.2 ∨ (a.2 = b.2 ∧ (a.1 = false ∨ b.1 = true))

instance : DecidableRel dioLe := fun a b => by unfold dioLe; infer_instance

/-- The order DIO applied to a word. -/
def dio (w : List Var) : List Var := w.insertionSort dioLe

/-- The up-arrow operator `↑` on a word. -/
def up (w : List Var) : List Var := w.map fun v => (v.1, v.2 + 1)

/-- The rule `R` of `G_Sec` on one variable, as a formal sum of words. -/
noncomputable def rule (v : Var) : List Var →₀ ℤ[X] :=
  if v.1 then Finsupp.single [v, (false, v.2 + 1)] (X ^ v.2)
  else Finsupp.single [] (X ^ v.2) + Finsupp.single [v, (false, v.2 + 1)] (X ^ v.2)

/-- The q-derivative of a single word. -/
noncomputable def derivWord (w : List Var) : List Var →₀ ℤ[X] :=
  ∑ j ∈ Finset.range w.length,
    (rule (w.getD j (false, 0))).sum fun t c =>
      Finsupp.single (dio (w.take j ++ t ++ up (w.drop (j + 1)))) c

/-- The q-derivative operator `D`, extended linearly. -/
noncomputable def deriv (E : List Var →₀ ℤ[X]) : List Var →₀ ℤ[X] :=
  E.sum fun w c => c • derivWord w

/-- The conjectured value of `Ω(Dⁿ(y₀))`. -/
def omegaFormula (n : ℕ) : ℕ :=
  if n = 1 then 1
  else if n = 2 then 3
  else if n % 2 = 1 then (20 * (n / 2) ^ 3 + 33 * (n / 2) ^ 2 + n / 2 - 6) / 6
  else (20 * (n / 2) - 17) * (n / 2 + 1) * (n / 2) / 6

/-- Conjecture III.7. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ((deriv^[n] (Finsupp.single [(true, 0)] 1)).support.card = omegaFormula n)

end D5.S3.Combinatorics.QGrammar.SecGrammarDefs
