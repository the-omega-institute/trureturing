/- GID: D5/S0/Certificates/Polynomials/JavaheriFourVariableTriangleRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Polynomials/JavaheriFourVariableTriangleRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real, mathlib/module/Mathlib.Data.Real.Sqrt]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Polynomials/JavaheriFourVariableTriangleRefutation.claim; result=D5/S0/Certificates/Polynomials/JavaheriFourVariableTriangleRefutation.result; claim=D5/S0/Certificates/Polynomials/JavaheriFourVariableTriangleRefutation.claim
   digest: The full four-variable weak square-root triangle prediction fails at (a,b)=(4,1) and the positive cyclic tuple (10,9,7,7). -/

/-
   proof_shape: result=bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#30729; Refuted)
   Direct frozen dependencies: JavaheriArrangementDimensionRefutation.arrangementInequality,
     JavaheriArrangementDimensionRefutation.c
-/

import D5.S0.Certificates.Polynomials.JavaheriArrangementDimensionRefutation
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Polynomials.JavaheriFourVariableTriangleRefutation

open JavaheriArrangementDimensionRefutation (arrangementInequality c)

/-- The complete four-variable prediction, including every weak and zero boundary. -/
def claim : Prop :=
  ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b →
    ((∀ x : Fin 4 → ℝ, (∀ i : Fin 4, 0 ≤ x i) → arrangementInequality a b 4 x) ↔
      (Real.sqrt a ≤ Real.sqrt b + 1 ∧
        Real.sqrt b ≤ Real.sqrt a + 1 ∧ 1 ≤ Real.sqrt a + Real.sqrt b))

/-- A positive cyclic quadruple in the order specified by the inequality. -/
private noncomputable def quadruple : Fin 4 → ℝ :=
  fun i => if i = 0 then 10 else if i = 1 then 9 else 7

/-- The square-root triangle condition is insufficient for the four-variable inequality. -/
theorem result : ¬ claim := by
  intro h
  have htriangle : Real.sqrt (4 : ℝ) ≤ Real.sqrt 1 + 1 ∧
      Real.sqrt (1 : ℝ) ≤ Real.sqrt 4 + 1 ∧
      1 ≤ Real.sqrt (4 : ℝ) + Real.sqrt 1 := by norm_num
  have hineq := (h 4 1 (by norm_num) (by norm_num)).mpr htriangle quadruple (by
    intro i
    fin_cases i <;> norm_num [quadruple])
  norm_num [arrangementInequality, quadruple, c, Fin.sum_univ_four,
    Real.rpow_natCast] at hineq

#print axioms claim
#print axioms result

end D5.S0.Certificates.Polynomials.JavaheriFourVariableTriangleRefutation
