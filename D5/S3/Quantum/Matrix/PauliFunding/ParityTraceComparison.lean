/- GID: D5/S3/Quantum/Matrix/PauliFunding/ParityTraceComparison
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/PauliFunding/ParityTraceComparison
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Even matrix power traces admit quadratic root comparisons with strict and singular boundaries. -/

import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Matrix.PauliFunding

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

/-- The real control parity. -/
def parity : Mat := !![1, 0; 0, -1]

/-- The even power sum of the two real roots of `x² - 2αx - β`. -/
def evenMoment (α β : ℝ) (j : ℕ) : ℝ :=
  (α + Real.sqrt (α ^ 2 + β)) ^ (2 * j) +
    (α - Real.sqrt (α ^ 2 + β)) ^ (2 * j)

/-- The Vieta trace formula, retaining zero determinant and repeated roots. -/
theorem even_trace_formula (W : Mat) (α β : ℝ) (hβ : 0 ≤ β)
    (htr : Matrix.trace W = 2 * α) (hdet : Matrix.det W = -β) (j : ℕ) :
    Matrix.trace (W ^ (2 * j)) = evenMoment α β j := by
  have hr : (Real.sqrt (α ^ 2 + β)) ^ 2 = α ^ 2 + β :=
    Real.sq_sqrt (by positivity)
  apply D5.S0.Observation.MatrixTracePowerSum.trace_pow_eq_add_pow
  · linarith
  · nlinarith

private theorem root_lower (α β c : ℝ) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hp : c ^ 2 - 2 * α * c - β ≤ 0) :
    c ≤ α + Real.sqrt (α ^ 2 + β) := by
  have hr := Real.sq_sqrt (show 0 ≤ α ^ 2 + β by positivity)
  have hs := Real.sqrt_nonneg (α ^ 2 + β)
  by_contra hn
  have hn' : α + Real.sqrt (α ^ 2 + β) < c := lt_of_not_ge hn
  have hd : Real.sqrt (α ^ 2 + β) < c - α := by linarith
  have hd0 : 0 < c - α := lt_of_le_of_lt hs hd
  nlinarith [sq_pos_of_pos (show 0 < c - α - Real.sqrt (α ^ 2 + β) by linarith),
    mul_pos (show 0 < c - α - Real.sqrt (α ^ 2 + β) by linarith)
      (show 0 < c - α + Real.sqrt (α ^ 2 + β) by linarith)]

private theorem root_strict (α β c : ℝ) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hp : c ^ 2 - 2 * α * c - β < 0) :
    c < α + Real.sqrt (α ^ 2 + β) := by
  have hr := Real.sq_sqrt (show 0 ≤ α ^ 2 + β by positivity)
  have hs := Real.sqrt_nonneg (α ^ 2 + β)
  have hl := root_lower α β c hβ hc hp.le
  apply lt_of_le_of_ne hl
  intro he
  rw [he] at hp
  nlinarith

/-- A quadratic sublevel point gives a lower bound for every even matrix trace.
No matrix positivity or diagonalizability hypothesis is needed. -/
theorem even_trace_comparison (W : Mat) (α β c : ℝ) (_hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hc : 0 ≤ c) (htr : Matrix.trace W = 2 * α)
    (hdet : Matrix.det W = -β) (hp : c ^ 2 - 2 * α * c - β ≤ 0) (j : ℕ) :
    c ^ (2 * j) ≤ Matrix.trace (W ^ (2 * j)) := by
  rw [even_trace_formula W α β hβ htr hdet j, evenMoment]
  exact le_add_of_le_of_nonneg
    (pow_le_pow_left₀ hc (root_lower α β c hβ hc hp) _)
    (Even.pow_nonneg (even_two_mul j) _)

/-- Strict quadratic sublevel points give strict comparisons at every positive order. -/
theorem even_trace_strict (W : Mat) (α β c : ℝ) (_hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hc : 0 ≤ c) (htr : Matrix.trace W = 2 * α)
    (hdet : Matrix.det W = -β) (hp : c ^ 2 - 2 * α * c - β < 0)
    (j : ℕ) (hj : 1 ≤ j) :
    c ^ (2 * j) < Matrix.trace (W ^ (2 * j)) := by
  rw [even_trace_formula W α β hβ htr hdet j, evenMoment]
  exact lt_add_of_lt_of_nonneg
    (pow_lt_pow_left₀ (root_strict α β c hβ hc hp) hc (by omega))
    (Even.pow_nonneg (even_two_mul j) _)

#print axioms even_trace_formula
#print axioms even_trace_comparison
#print axioms even_trace_strict

end D5.S3.Quantum.Matrix.PauliFunding
