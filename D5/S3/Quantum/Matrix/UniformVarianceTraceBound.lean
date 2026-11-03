/- GID: D5/S3/Quantum/Matrix/UniformVarianceTraceBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/UniformVarianceTraceBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual centered Kraus maps obey the undivided trace norm bound on all finite references. -/

import D5.S3.Quantum.Matrix.UniformVarianceCentering
import D5.S3.Quantum.Foundation.FiniteTraceDistance

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Matrix.UniformVarianceTraceBound
open D5.S3.Quantum.Foundation.FiniteTraceDistance

private lemma re_diag_le_norm {a : Type*} [Fintype a] [DecidableEq a]
    (B : Matrix a a ℂ) (i : a) : (B i i).re ≤ ‖B‖ := by
  let e := EuclideanSpace.basisFun a ℂ i
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun a ℂ).orthonormal.1 i
  have hi : inner ℂ e (Matrix.toEuclideanCLM B e) = B i i := by
    simp [e, EuclideanSpace.basisFun_apply, Matrix.toEuclideanCLM_toLp,
      EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec, dotProduct]
  rw [← hi]
  exact (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
    (by simpa [he, Matrix.l2_opNorm_toEuclideanCLM] using
      (Matrix.toEuclideanCLM B).le_opNorm e))

private lemma re_trace_mul_le {a : Type*} [Fintype a] [DecidableEq a]
    (B X : Matrix a a ℂ) : (B*X).trace.re ≤ ‖B‖ * traceNorm X := by
  classical
  let hH : (Xᴴ * X).IsHermitian := by
    simpa using Matrix.isHermitian_mul_conjTranspose_self X.conjTranspose
  obtain ⟨V,W,hX⟩ := exists_svd_sqrt_eigenvalues X
  let D : Matrix a a ℂ := diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hX' : X = V.val * D * W.valᴴ := hX
  have hW : W.valᴴ * W.val = 1 := Matrix.mem_unitaryGroup_iff'.mp W.prop
  have hV : V.valᴴ * V.val = 1 := Matrix.mem_unitaryGroup_iff'.mp V.prop
  have hmass : (∑ i, Real.sqrt (hH.eigenvalues i)) ≤ traceNorm X := by
    have hm := (traceNorm_eq_max_re_tr_U X).2
      (show ((W * star V).val * X).trace.re ∈
        {x : ℝ | ∃ U : unitaryGroup a ℂ, (U.val * X).trace.re = x} from
        ⟨W * star V,rfl⟩)
    have heq : ((W * star V).val * X).trace = D.trace := by
      rw [hX']
      change (W.val * V.valᴴ * (V.val * D * W.valᴴ)).trace = D.trace
      simp [Matrix.mul_assoc,hV,Matrix.trace_mul_comm,hW]
    simpa [heq,D,Matrix.trace] using hm
  have hnorm : ‖W.valᴴ * B * V.val‖ = ‖B‖ := by
    change ‖(star W).val * B * V.val‖ = ‖B‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  calc
    _ = ((W.valᴴ * B * V.val) * D).trace.re := by
      rw [hX']; congr 1
      rw [Matrix.trace_mul_comm _ W.valᴴ]
      simp only [Matrix.mul_assoc]
    _ = ∑ i, Real.sqrt (hH.eigenvalues i) * ((W.valᴴ * B * V.val) i i).re := by
      simp [D, Matrix.trace, Matrix.mul_diagonal, Complex.mul_re, mul_comm]
    _ ≤ ∑ i, Real.sqrt (hH.eigenvalues i) * ‖B‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left ((re_diag_le_norm _ i).trans_eq hnorm)
        (Real.sqrt_nonneg _)
    _ = ‖B‖ * ∑ i, Real.sqrt (hH.eigenvalues i) := by rw [Finset.sum_mul,mul_comm]
    _ ≤ ‖B‖ * traceNorm X := mul_le_mul_of_nonneg_left hmass (norm_nonneg _)

end D5.S3.Quantum.Matrix.UniformVarianceTraceBound
