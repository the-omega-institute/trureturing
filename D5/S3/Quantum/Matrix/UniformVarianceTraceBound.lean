/- GID: D5/S3/Quantum/Matrix/UniformVarianceTraceBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/UniformVarianceTraceBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered Kraus outputs obey the trace norm bound on all finite references. -/

import D5.S3.Quantum.Matrix.UniformVarianceCentering
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-! Ordinary trace norms of the same amplified centered Kraus maps. -/

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator CStarAlgebra
namespace D5.S3.Quantum.Matrix.UniformVarianceTraceBound
open D5.S3.Quantum.Foundation.FiniteTraceDistance

private lemma re_diag_le_norm {a : Type*} [Fintype a] [DecidableEq a]
    (B : Matrix a a ℂ) (i : a) : (B i i).re ≤ ‖B‖ := by
  let e := EuclideanSpace.basisFun a ℂ i
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun a ℂ).orthonormal.1 i
  have hi : inner ℂ e (Matrix.toEuclideanCLM (n := a) (𝕜 := ℂ) B e) = B i i := by
    simp [e, EuclideanSpace.basisFun_apply, Matrix.toEuclideanCLM_toLp,
      EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hi]
  exact (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
    (by simpa [he, Matrix.l2_opNorm_toEuclideanCLM] using
      (Matrix.toEuclideanCLM (n := a) (𝕜 := ℂ) B).le_opNorm e))

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
    rw [heq] at hm
    simpa [D,Matrix.trace] using hm
  have hnorm : ‖W.valᴴ * B * V.val‖ = ‖B‖ := by
    change ‖(star W).val * B * V.val‖ = ‖B‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  calc
    _ = ((W.valᴴ * B * V.val) * D).trace.re := by
      rw [hX']; congr 1
      simp only [← Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm _ W.valᴴ]
      simp only [Matrix.mul_assoc]
    _ = ∑ i, Real.sqrt (hH.eigenvalues i) * ((W.valᴴ * B * V.val) i i).re := by
      simp [D, Matrix.trace, Matrix.mul_diagonal, Complex.mul_re, mul_comm]
    _ ≤ ∑ i, Real.sqrt (hH.eigenvalues i) * ‖B‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left ((re_diag_le_norm _ i).trans_eq hnorm)
        (Real.sqrt_nonneg _)
    _ = ‖B‖ * ∑ i, Real.sqrt (hH.eigenvalues i) := by rw [← Finset.sum_mul,mul_comm]
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
    rw [← hBmap,StarAlgEquiv.norm_map (operator v) B,
      show ‖A‖ = ‖U.val‖ from StarAlgEquiv.norm_map (operator w) U.val] at hh
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
    simp only [← Matrix.mul_assoc]
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
      ∀ X : Matrix (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E))))
        (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E)))) ℂ, traceNorm (∑ j, M j * X * (M j)ᴴ) ≤ (5*δ)*traceNorm X := by
  classical
  have hp := D5.S3.Quantum.Matrix.UniformVarianceCentering.hermitian_block_centering_and_gram_bound
    V h hh δ hδ hv e he
  dsimp only
  intro n
  apply kraus_trace_bound
  · positivity
  · exact hp.2.2.2.2 n

private lemma centered_defect_identity {a J : Type*}
    [Fintype a] [DecidableEq a] [Fintype J]
    (H : J → Matrix a a ℂ) (hH : ∀ j, (H j).IsHermitian)
    (hs : ∑ j, H j * H j = 1) (c : J → ℝ) (X : Matrix a a ℂ) :
    let M := fun j => H j - (c j : ℂ) • (1 : Matrix a a ℂ)
    let Q := ∑ j, (M j)ᴴ * M j
    X - ∑ j, H j * X * (H j)ᴴ =
      (1/2 : ℂ) • (Q*X+X*Q) - ∑ j, M j * X * (M j)ᴴ := by
  classical
  dsimp only
  have hj (j : J) :
      ((H j - (c j : ℂ) • 1)ᴴ * (H j - (c j : ℂ) • 1))*X +
        X*((H j - (c j : ℂ) • 1)ᴴ * (H j - (c j : ℂ) • 1)) -
        (2 : ℂ) • ((H j - (c j : ℂ) • 1)*X*(H j - (c j : ℂ) • 1)ᴴ) =
      (H j * H j)*X+X*(H j * H j) - (2 : ℂ) • (H j * X * (H j)ᴴ) := by
    have hm : (H j - (c j : ℂ) • 1)ᴴ = H j - (c j : ℂ) • 1 := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, hH j]
      simp
    rw [hm]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  have ht := congrArg (fun f : J → Matrix a a ℂ => ∑ j, f j) (funext hj)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.smul_sum, hs, one_mul, mul_one] at ht
  calc
    _ = (1/2 : ℂ) • (X+X-(2 : ℂ) • (∑ j, H j * X * (H j)ᴴ)) := by module
    _ = (1/2 : ℂ) •
        (((∑ j, (H j - (c j : ℂ) • 1)ᴴ * (H j - (c j : ℂ) • 1))*X +
          X*(∑ j, (H j - (c j : ℂ) • 1)ᴴ * (H j - (c j : ℂ) • 1))) -
          (2 : ℂ) • (∑ j, (H j - (c j : ℂ) • 1)*X*(H j - (c j : ℂ) • 1)ᴴ)) :=
      congrArg (fun Y : Matrix a a ℂ => (1/2 : ℂ) • Y) ht.symm
    _ = _ := by module

/-- A unital Hermitian Kraus family on a factor has its actual centered defect
bounded in ordinary trace norm on every finite reference. -/
theorem hermitian_unital_kraus_defect_trace_bound {J : Type*} [Fintype J]
    (h : J → E →ₗ[ℂ] E) (hh : ∀ j, (h j).IsSymmetric)
    (hs : ∑ j, (h j).comp (h j) = LinearMap.id)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ x : E, ‖x‖ = 1 →
      ∑ j, ‖h j x - (inner ℂ x (h j x)).re • x‖^2 ≤ δ)
    (e : E) (he : (∃ x : E, ‖x‖ = 1) → ‖e‖ = 1) :
    let c : J → ℝ := fun j => (inner ℂ e (h j e)).re
    ∀ n : ℕ,
      let v := stdOrthonormalBasis ℂ (PiLp 2 (fun _ : Fin n => E))
      let H := fun j => LinearMap.toMatrix v.toBasis v.toBasis (referenceLift n (h j))
      let M := fun j => H j - (c j : ℂ) • 1
      let Q := ∑ j, (M j)ᴴ * M j
      ∀ X : Matrix (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E))))
        (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E)))) ℂ,
        (X - ∑ j, H j * X * (H j)ᴴ =
          (1/2 : ℂ) • (Q*X+X*Q) - ∑ j, M j * X * (M j)ᴴ) ∧
        traceNorm (X - ∑ j, H j * X * (H j)ᴴ) ≤ (10*δ)*traceNorm X := by
  classical
  let V : E →ₗᵢ[ℂ] E := LinearIsometry.id
  let c : J → ℝ := fun j => (inner ℂ e (h j e)).re
  let L : J → E →ₗ[ℂ] E := fun j => h j - (c j : ℂ) • LinearMap.id
  have hp := D5.S3.Quantum.Matrix.UniformVarianceCentering.hermitian_block_centering_and_gram_bound
    V h hh δ hδ hv e he
  have ht := hermitian_centered_kraus_trace_bound V h hh δ hδ hv e he
  dsimp only
  intro n
  let v := stdOrthonormalBasis ℂ (PiLp 2 (fun _ : Fin n => E))
  let H := fun j => LinearMap.toMatrix v.toBasis v.toBasis (referenceLift n (h j))
  let M := fun j => H j - (c j : ℂ) • 1
  let Q := ∑ j, (M j)ᴴ * M j
  have hM (j : J) :
      LinearMap.toMatrix v.toBasis v.toBasis (referenceLift n (L j)) = M j := by
    have hl : referenceLift n (L j) =
        referenceLift n (h j) - (c j : ℂ) • LinearMap.id := by
      ext x r
      rfl
    change LinearMap.toMatrix v.toBasis v.toBasis (referenceLift n (L j)) =
      H j - (c j : ℂ) • 1
    rw [hl, map_sub, map_smul, LinearMap.toMatrix_id]
    rfl
  have hH (j : J) : (H j).IsHermitian := by
    apply (LinearMap.isHermitian_toMatrix_iff v).mpr
    intro x y
    simp only [PiLp.inner_apply]
    exact Finset.sum_congr rfl (fun r _ => hh j (x r) (y r))
  have hsum : ∑ j, H j * H j = 1 := by
    have hl : ∑ j, (referenceLift n (h j)).comp (referenceLift n (h j)) =
        LinearMap.id := by
      ext x r
      have hz := congrArg (fun T : E →ₗ[ℂ] E => T (x r)) hs
      simpa [referenceLift, LinearMap.sum_apply] using hz
    have hz := congrArg (LinearMap.toMatrix v.toBasis v.toBasis) hl
    rw [map_sum, LinearMap.toMatrix_id] at hz
    simpa only [LinearMap.toMatrix_comp v.toBasis v.toBasis v.toBasis, H] using hz
  have hqmap : operator v Q =
      (∑ j, (referenceLift n (L j)).adjoint.comp (referenceLift n (L j))).toContinuousLinearMap := by
    change (Matrix.toLin v.toBasis v.toBasis Q).toContinuousLinearMap = _
    congr 1
    simp only [Q, map_sum, Matrix.toLin_mul v.toBasis v.toBasis v.toBasis,
      Matrix.toLin_conjTranspose, ← hM, Matrix.toLin_toMatrix]
  have hqnorm : ‖Q‖ ≤ 5*δ := by
    have hz := hp.2.2.2.2 n (ContinuousLinearMap.id ℂ _)
    change ‖(∑ j, (referenceLift n (L j)).adjoint.comp
      (referenceLift n (L j))).toContinuousLinearMap‖
      ≤ (5*δ)*‖ContinuousLinearMap.id ℂ (PiLp 2 (fun _ : Fin n => E))‖ at hz
    rw [← hqmap, StarAlgEquiv.norm_map (operator v) Q] at hz
    have hi : ‖ContinuousLinearMap.id ℂ (PiLp 2 (fun _ : Fin n => E))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    exact hz.trans (by nlinarith)
  have hk (X : Matrix (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E))))
      (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E)))) ℂ) :
      traceNorm (∑ j, M j * X * (M j)ᴴ) ≤ (5*δ)*traceNorm X := by
    simpa only [← hM] using ht n X
  intro X
  have hid := centered_defect_identity H hH hsum c X
  refine ⟨hid, ?_⟩
  obtain ⟨U,hU⟩ := (traceNorm_eq_max_re_tr_U (X - ∑ j, H j * X * (H j)ᴴ)).1
  have hUn : ‖U.val‖ ≤ 1 := by
    rcases isEmpty_or_nonempty (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E)))) with hi | hi
    · have hz : U.val = 0 := Subsingleton.elim _ _
      simp [hz]
    · exact (CStarRing.norm_coe_unitary U).le
  have hUQ : ‖U.val*Q‖ ≤ 5*δ :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right hUn (norm_nonneg Q)).trans
      (by simpa using hqnorm))
  have hQU : ‖Q*U.val‖ ≤ 5*δ :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hUn (norm_nonneg Q)).trans
      (by simpa using hqnorm))
  have h1 := (re_trace_mul_le (U.val*Q) X).trans
    (mul_le_mul_of_nonneg_right hUQ (traceNorm_nonneg X))
  have h2 := (re_trace_mul_le (Q*U.val) X).trans
    (mul_le_mul_of_nonneg_right hQU (traceNorm_nonneg X))
  have h3 := (traceNorm_eq_max_re_tr_U (∑ j, M j * X * (M j)ᴴ)).2
    (show ((-U).val * (∑ j, M j * X * (M j)ᴴ)).trace.re ∈
      {x : ℝ | ∃ U : unitaryGroup _ ℂ,
        (U.val * (∑ j, M j * X * (M j)ᴴ)).trace.re = x} from ⟨-U,rfl⟩)
  have heq : traceNorm (X - ∑ j, H j * X * (H j)ᴴ) =
      (1/2 : ℝ)*((U.val*Q*X).trace.re+(Q*U.val*X).trace.re) -
        (U.val*(∑ j, M j * X * (M j)ᴴ)).trace.re := by
    rw [← hU, hid]
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_add, Complex.sub_re,
      Complex.inv_re, Complex.ofNat_re, Complex.ofNat_im, Complex.div_re,
      Complex.mul_re, Complex.mul_im, Complex.inv_im]
    have hc : (U.val*(X*Q)).trace = (Q*U.val*X).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm _ Q]
    simp only [Matrix.mul_assoc] at hc ⊢
    rw [hc]
    norm_num
  have h3' : -(U.val*(∑ j, M j * X * (M j)ᴴ)).trace.re ≤
      (5*δ)*traceNorm X := by
    exact (by simpa using h3).trans (hk X)
  rw [heq]
  linarith

end Hilbert
end D5.S3.Quantum.Matrix.UniformVarianceTraceBound
