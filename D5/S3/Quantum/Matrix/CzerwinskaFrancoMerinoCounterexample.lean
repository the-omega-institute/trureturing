/- GID: D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.conjecture; result=D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.result; claim=D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.conjecture
   digest: Radial convexity of order three does not characterize matrix monotonicity. -/

/-
admission_basis: open-problem-resolution
proof_shape: finite_certificate: bind-only; consumer: not_matrix_monotone
proof_shape: not_matrix_monotone: bind-only; consumer: result
proof_shape: result: content
The content basis is the endpoint-factorization, interpolation and endpoint-positivity argument
used by radial_counterexample; the exact finite certificate excludes both monotonicity directions.
-/

import D5.S3.Quantum.Matrix.CfmEndpointPositivity
import D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-! A rational counterexample to Conjecture 4.10 on the whole positive cone. -/

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.CzerwinskaFrancoMerinoCounterexample

open RadialConvexity CayleyResolvent CfmRadialDerivative
open CfmEndpointPositivity CfmMonotonicityCertificate

/-- Conjecture 4.10, with both monotonicity directions allowed as in Definition 2.15. -/
def conjecture : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ f : ℝ → ℝ,
  RadiallyConvexOrder n f ↔ MatrixMonotoneDegree n f

private def rankVector : Fin 3 → ℂ := ![2, 3, 6]

private theorem rank_increment :
    upperMatrix - lowerMatrix = (2 / 75 : ℝ) • vecMulVec rankVector (star rankVector) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerMatrix, upperMatrix, rankVector, diagonal, vecMulVec, map_ofNat]

private theorem increment_psd : (upperMatrix - lowerMatrix).PosSemidef := by
  rw [rank_increment]
  exact (posSemidef_vecMulVec_self_star rankVector).smul (by norm_num)

private theorem lower_pos : lowerMatrix.PosDef := by
  apply PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

private theorem upper_pos : upperMatrix.PosDef := by
  have h := lower_pos.add_posSemidef increment_psd
  simpa only [add_sub_cancel] using h

private theorem inv_lower_1 : (lowerMatrix + 3)⁻¹ =
    (!![3 / 10, 0, 0; 0, 1 / 4, 0; 0, 0, 1 / 6] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerMatrix, Matrix.mul_apply, Fin.sum_univ_succ, diagonal, Matrix.ofNat_apply, Matrix.one_apply]

private theorem inv_lower_2 : ((2 : ℝ) • lowerMatrix + 4)⁻¹ =
    (!![3 / 14, 0, 0; 0, 1 / 6, 0; 0, 0, 1 / 10] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerMatrix, Matrix.mul_apply, Fin.sum_univ_succ, diagonal, Matrix.ofNat_apply, Matrix.one_apply]

private theorem inv_lower_3 : ((3 : ℝ) • lowerMatrix + 5)⁻¹ =
    (!![1 / 6, 0, 0; 0, 1 / 8, 0; 0, 0, 1 / 14] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerMatrix, Matrix.mul_apply, Fin.sum_univ_succ, diagonal, Matrix.ofNat_apply, Matrix.one_apply]

private theorem inv_upper_1 : (upperMatrix + 3)⁻¹ =
    (!![183 / 626, -3 / 313, -4 / 313; -3 / 313, 149 / 626, -5 / 313;
      -4 / 313, -5 / 313, 91 / 626] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.ofNat_apply, Matrix.one_apply]

private theorem inv_upper_2 : ((2 : ℝ) • upperMatrix + 4)⁻¹ =
    (!![477 / 2306, -10 / 1153, -12 / 1153; -10 / 1153, 361 / 2306, -14 / 1153;
      -12 / 1153, -14 / 1153, 197 / 2306] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.ofNat_apply, Matrix.one_apply]

private theorem inv_upper_3 : ((3 : ℝ) • upperMatrix + 5)⁻¹ =
    (!![907 / 5666, -21 / 2833, -24 / 2833; -21 / 2833, 661 / 5666, -27 / 2833;
      -24 / 2833, -27 / 2833, 343 / 5666] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.ofNat_apply, Matrix.one_apply]

private theorem quadratic_certificate :
    quadraticReadout (rationalFunction upperMatrix - rationalFunction lowerMatrix) =
      -(2 / 111549375 : ℝ) := by
  unfold quadraticReadout rationalFunction
  rw [inv_lower_1, inv_lower_2, inv_lower_3, inv_upper_1, inv_upper_2, inv_upper_3]
  norm_num [testVector, lowerMatrix, upperMatrix, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, diagonal, Matrix.ofNat_apply, Matrix.one_apply]

private theorem positive_diagonal_certificate :
    0 < ((rationalFunction upperMatrix - rationalFunction lowerMatrix) 0 0).re := by
  unfold rationalFunction
  rw [inv_lower_1, inv_lower_2, inv_lower_3, inv_upper_1, inv_upper_2, inv_upper_3]
  norm_num [testVector, lowerMatrix, upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, diagonal, Matrix.ofNat_apply, Matrix.one_apply]

/-- Ordered positive definite matrices give both a negative quadratic form and a positive
entry in their rational-function increment, excluding either monotonicity direction. -/
theorem finite_certificate :
    lowerMatrix.PosDef ∧ upperMatrix.PosDef ∧ lowerMatrix ≤ upperMatrix ∧
    quadraticReadout (rationalFunction upperMatrix - rationalFunction lowerMatrix) =
      -(2 / 111549375 : ℝ) ∧
    0 < ((rationalFunction upperMatrix - rationalFunction lowerMatrix) 0 0).re := by
  exact ⟨lower_pos, upper_pos, increment_psd, quadratic_certificate,
    positive_diagonal_certificate⟩

/-- The real rational function has neither Loewner monotonicity direction in dimension three. -/
theorem not_matrix_monotone : ¬ RadialConvexity.MatrixMonotoneDegree 3 scalarFunction := by
  rintro (hinc | hdec)
  · rcases finite_certificate with ⟨hA, hB, hle, hq, _⟩
    have hp := Matrix.le_iff.mp (hinc lowerMatrix upperMatrix hA hB hle)
    change (cfc scalarFunction upperMatrix - cfc scalarFunction lowerMatrix).PosSemidef at hp
    rw [cfc_rationalFunction hA, cfc_rationalFunction hB] at hp
    have hn := hp.re_dotProduct_nonneg testVector
    change 0 ≤ quadraticReadout (rationalFunction upperMatrix - rationalFunction lowerMatrix) at hn
    rw [hq] at hn
    norm_num at hn
  · rcases finite_certificate with ⟨hA, hB, hle, _, hd⟩
    have hp := Matrix.le_iff.mp (hdec lowerMatrix upperMatrix hA hB hle)
    change (cfc scalarFunction lowerMatrix - cfc scalarFunction upperMatrix).PosSemidef at hp
    rw [cfc_rationalFunction hA, cfc_rationalFunction hB] at hp
    have hn := (Complex.nonneg_iff.mp (hp.diag_nonneg (i := 0))).1
    simp only [Matrix.sub_apply, Complex.sub_re] at hn hd
    linarith


private theorem cayley_functional_calculus {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    matFun scalarFunction A = resolventSum (1/20000 : ℝ) (cayley A) := by
  rw [matFun, cfc_rationalFunction hA]
  dsimp only [resolventSum]
  rw [cayley_resolvent 2 (by norm_num) A hA,
    cayley_resolvent 3 (by norm_num) A hA,
    cayley_resolvent 4 (by norm_num) A hA]
  norm_num [rationalFunction]
  simp only [← Algebra.algebraMap_eq_smul_one, map_ofNat]

private theorem radial_counterexample : RadiallyConvexOrder 3 scalarFunction := by
  intro A C B hA hC hB hAC hCB
  have ha := cayley_transport A hA
  have hc := cayley_transport C hC
  have hb := cayley_transport B hB
  have h := radial_of_endpoint_positive (1/20000 : ℝ)
    (fun U hU V hV hUV => endpoint_derivatives_positive U V hU hV hUV)
    (show cayley A ∈ cayleyDomain 3 from ⟨ha.1,ha.2.1⟩)
    (show cayley C ∈ cayleyDomain 3 from ⟨hc.1,hc.2.1⟩)
    (show cayley B ∈ cayleyDomain 3 from ⟨hb.1,hb.2.1⟩)
    (ha.2.2 C hC hAC) (hc.2.2 B hB hCB)
  rwa [cayley_functional_calculus A hA, cayley_functional_calculus C hC,
    cayley_functional_calculus B hB]

/-- The rational function is radially convex of order three and is monotone in
neither Loewner direction, refuting the universally quantified conjecture. -/
theorem result : ¬ conjecture := by
  intro h
  exact not_matrix_monotone ((h 3 (by norm_num) scalarFunction).mp radial_counterexample)

end D5.S3.Quantum.Matrix.CzerwinskaFrancoMerinoCounterexample
