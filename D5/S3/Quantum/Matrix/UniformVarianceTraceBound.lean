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


section Hilbert
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

private def operator {a : Type*} [Fintype a] [DecidableEq a]
    (v : OrthonormalBasis a ℂ E) :
    Matrix a a ℂ ≃⋆ₐ[ℂ] (E →L[ℂ] E) :=
  (LinearMap.toMatrixOrthonormal v).symm.trans
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := LinearMap.adjoint_toContinuousLinearMap }

private lemma kraus_trace_bound {a b J : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype J]
    (v : OrthonormalBasis a ℂ E) (w : OrthonormalBasis b ℂ F)
    (L : J → E →ₗ[ℂ] F) (c : ℝ) (hc : 0 ≤ c)
    (hK : ∀ A : F →L[ℂ] F,
      ‖(∑ j, (L j).adjoint.comp (A.toLinearMap.comp (L j))).toContinuousLinearMap‖
        ≤ c*‖A‖)
    (X : Matrix a a ℂ) :
    let M := fun j => LinearMap.toMatrix v.toBasis w.toBasis (L j)
    traceNorm (∑ j, M j * X * (M j)ᴴ) ≤ c*traceNorm X := by
  classical
  let M := fun j => LinearMap.toMatrix v.toBasis w.toBasis (L j)
  change traceNorm (∑ j, M j * X * (M j)ᴴ) ≤ c*traceNorm X
  obtain ⟨U,hU⟩ := (traceNorm_eq_max_re_tr_U (∑ j, M j * X * (M j)ᴴ)).1
  let A := operator w U.val
  let B : Matrix a a ℂ := ∑ j, (M j)ᴴ * U.val * M j
  have hBmap : operator v B =
      (∑ j, (L j).adjoint.comp (A.toLinearMap.comp (L j))).toContinuousLinearMap := by
    change (Matrix.toLin v.toBasis v.toBasis B).toContinuousLinearMap = _
    congr 1
    simp only [B,map_sum,Matrix.toLin_mul v.toBasis w.toBasis v.toBasis,
      Matrix.toLin_mul w.toBasis w.toBasis v.toBasis,
      Matrix.toLin_conjTranspose, M,Matrix.toLin_toMatrix]
    rfl
  have hBnorm : ‖B‖ ≤ c := by
    have hh := hK A
    rw [← hBmap,StarAlgEquiv.norm_map,show ‖A‖ = ‖U.val‖ from StarAlgEquiv.norm_map _ _] at hh
    have hUnorm : ‖U.val‖ ≤ 1 := by
      rcases isEmpty_or_nonempty b with hb | hb
      · have hz : U.val = 0 := Subsingleton.elim _ _
        simp [hz]
      · exact (CStarRing.norm_coe_unitary U).le
    exact hh.trans (by simpa using mul_le_mul_of_nonneg_left hUnorm hc)
  have ht : (U.val * (∑ j, M j * X * (M j)ᴴ)).trace = (B*X).trace := by
    simp only [B,Matrix.mul_sum,Matrix.sum_mul,Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.trace_mul_comm _ (M j)ᴴ]
    simp only [Matrix.mul_assoc]
  calc
    _ = (B*X).trace.re := hU.symm.trans (congrArg Complex.re ht)
    _ ≤ ‖B‖ * traceNorm X := re_trace_mul_le B X
    _ ≤ c * traceNorm X := mul_le_mul_of_nonneg_right hBnorm (traceNorm_nonneg _)

private def referenceLift (n : ℕ) (L : E →ₗ[ℂ] F) :
    PiLp 2 (fun _ : Fin n => E) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => F) where
  toFun x := WithLp.toLp 2 (fun r => L (x r))
  map_add' x y := by ext r; exact L.map_add (x r) (y r)
  map_smul' c x := by ext r; exact L.map_smul c (x r)

/-- The same actual ambient centered Kraus family controls the undivided trace
norm on every complex input at every finite reference size. -/
theorem hermitian_centered_kraus_trace_bound {J : Type*} [Fintype J]
    (V : E →ₗᵢ[ℂ] F) (h : J → F →ₗ[ℂ] F)
    (hh : ∀ j, (h j).IsSymmetric) (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ x : E, ‖x‖ = 1 →
      ∑ j, ‖h j (V x) - (inner ℂ (V x) (h j (V x))).re • V x‖^2 ≤ δ)
    (e : E) (he : (∃ x : E, ‖x‖ = 1) → ‖e‖ = 1) :
    let c : J → ℝ := fun j => (inner ℂ (V e) (h j (V e))).re
    let L : J → E →ₗ[ℂ] F := fun j => (h j).comp V.toLinearMap - (c j : ℂ) • V.toLinearMap
    ∀ n : ℕ,
      let v := stdOrthonormalBasis ℂ (PiLp 2 (fun _ : Fin n => E))
      let w := stdOrthonormalBasis ℂ (PiLp 2 (fun _ : Fin n => F))
      let M := fun j => LinearMap.toMatrix v.toBasis w.toBasis (referenceLift n (L j))
      ∀ X, traceNorm (∑ j, M j * X * (M j)ᴴ) ≤ (5*δ)*traceNorm X := by
  classical
  have hp := D5.S3.Quantum.Matrix.UniformVarianceCentering.hermitian_block_centering_and_gram_bound
    V h hh δ hδ hv e he
  dsimp only
  intro n
  apply kraus_trace_bound
  · positivity
  · exact hp.2.2.2.2 n

end Hilbert
end D5.S3.Quantum.Matrix.UniformVarianceTraceBound
