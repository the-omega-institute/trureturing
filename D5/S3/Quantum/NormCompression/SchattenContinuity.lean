/- GID: D5/S3/Quantum/NormCompression/SchattenContinuity
   generality: G
   mirror-B: none(waiver:shared-existing-supplier)
   mirror-E: none(waiver:shared-existing-supplier)
   anchors: []
   utility: none
   digest: Shared existing actual Schatten trace representation and continuity proof. -/

import D5.S3.Quantum.NormCompression.UpperBranchReduction
import D5.S3.Resource.LogDet.PathSpectralClassical
import Mathlib.Analysis.CStarAlgebra.Matrix

noncomputable section
namespace D5.S3.Quantum.NormCompression.SchattenContinuity
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.NormCompression.UpperBranchReduction

theorem schattenPow_trace {n : ℕ} {p : ℝ} (hp : 0 < p) (A : Matrix (Fin n) (Fin n) ℂ) :
    schattenPow p A = (cfc (fun x : ℝ => x ^ (p / 2)) (Aᴴ * A)).trace.re := by
  rw [schattenPow_eq_columnGram p hp A, D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum _ (Matrix.isHermitian_conjTranspose_mul_self A)]

theorem continuous_schattenPow {n : ℕ} {p : ℝ} (hp : 0 < p) :
    Continuous (schattenPow p : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  have hfun : Continuous (fun x : ℝ => x ^ (p / 2)) :=
    continuous_id.rpow_const (fun _ => Or.inr (by positivity))
  have hgram : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => Aᴴ * A) := by fun_prop
  have hcont : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
      cfc (fun x : ℝ => x ^ (p / 2)) (Aᴴ * A)) := by
    exact hgram.cfc_of_mem_nhdsSet (fun x : ℝ => x ^ (p / 2))
      (s := Set.univ) (by simp) (fun A => (Matrix.isHermitian_conjTranspose_mul_self A).isSelfAdjoint)
      hfun.continuousOn
  have htrace : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (cfc (fun x : ℝ => x ^ (p / 2)) (Aᴴ * A)).trace.re) := by
    unfold Matrix.trace
    fun_prop
  convert htrace using 1
  funext A
  exact schattenPow_trace hp A

end D5.S3.Quantum.NormCompression.SchattenContinuity
