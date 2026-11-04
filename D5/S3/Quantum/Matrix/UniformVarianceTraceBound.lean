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

private lemma unital_kraus_trace_bound {a J : Type*}
    [Fintype a] [DecidableEq a] [Fintype J]
    (v : OrthonormalBasis a ℂ E) (M : J → Matrix a a ℂ)
    (hs : ∑ j, (M j)ᴴ * M j = 1) (X : Matrix a a ℂ) :
    traceNorm (∑ j, M j * X * (M j)ᴴ) ≤ traceNorm X := by
  classical
  let L : J → E →ₗ[ℂ] E := fun j => Matrix.toLin v.toBasis v.toBasis (M j)
  have hgram : ∑ j, (L j).adjoint.comp (L j) = LinearMap.id := by
    apply (LinearMap.toMatrix v.toBasis v.toBasis).injective
    simpa only [map_sum, LinearMap.toMatrix_comp v.toBasis v.toBasis v.toBasis,
      LinearMap.toMatrix_adjoint, LinearMap.toMatrix_toLin, LinearMap.toMatrix_id, L] using hs
  have hen (x : E) : ∑ j, ‖L j x‖^2 = ‖x‖^2 := by
    calc
      _ = (inner ℂ ((∑ j, (L j).adjoint.comp (L j)) x) x).re := by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        rw [sum_inner, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [LinearMap.adjoint_inner_left, norm_sq_eq_re_inner (𝕜 := ℂ)]
        rfl
      _ = ‖x‖^2 := by
        rw [hgram, LinearMap.id_apply]
        exact (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  have hadj (T : E →L[ℂ] E) :
      ‖(∑ j, (L j).adjoint.comp (T.toLinearMap.comp (L j))).toContinuousLinearMap‖
        ≤ (1:ℝ)*‖T‖ := by
    apply D5.S3.Quantum.Matrix.UniformVarianceCentering.kraus_adjoint_norm_le L 1 (by norm_num)
    intro x hx
    rw [hen, hx]
    norm_num
  have hz := kraus_trace_bound v v L 1 (by norm_num) hadj X
  simpa only [L, LinearMap.toMatrix_toLin, one_mul] using hz

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
        Matrix.conjTranspose_one, (hH j).eq]
      simp
    rw [hm, (hH j).eq]
    simp only [sub_mul, mul_sub, Algebra.smul_mul_assoc (R := ℂ),
      Algebra.mul_smul_comm (R := ℂ), one_mul, mul_one]
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

private lemma trace_centered_defect {a : Type*} [Fintype a] [DecidableEq a]
    (Q X K D : Matrix a a ℂ) (b : ℝ)
    (hqnorm : ‖Q‖ ≤ b) (hk : traceNorm K ≤ b*traceNorm X)
    (hid : D = (1/2 : ℂ) • (Q*X+X*Q) - K) :
    traceNorm D ≤ (2*b)*traceNorm X := by
  obtain ⟨U,hU⟩ := (traceNorm_eq_max_re_tr_U D).1
  have hUn : ‖U.val‖ ≤ 1 := by
    rcases isEmpty_or_nonempty a with hi | hi
    · have hz : U.val = 0 := Subsingleton.elim _ _
      simp [hz]
    · exact (CStarRing.norm_coe_unitary U).le
  have hUQ : ‖U.val*Q‖ ≤ b :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right hUn (norm_nonneg Q)).trans
      (by simpa using hqnorm))
  have hQU : ‖Q*U.val‖ ≤ b :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hUn (norm_nonneg Q)).trans
      (by simpa using hqnorm))
  have h1 := (re_trace_mul_le (U.val*Q) X).trans
    (mul_le_mul_of_nonneg_right hUQ (traceNorm_nonneg X))
  have h2 := (re_trace_mul_le (Q*U.val) X).trans
    (mul_le_mul_of_nonneg_right hQU (traceNorm_nonneg X))
  have h3 := (traceNorm_eq_max_re_tr_U K).2
    (show ((-U).val * K).trace.re ∈
      {x : ℝ | ∃ U : unitaryGroup _ ℂ,
        (U.val * K).trace.re = x} from ⟨-U,rfl⟩)
  have heq : traceNorm D =
      (1/2 : ℝ)*((U.val*Q*X).trace.re+(Q*U.val*X).trace.re) -
        (U.val*K).trace.re := by
    have hc : (U.val*(X*Q)).trace = (Q*U.val*X).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm _ Q]
      simp only [Matrix.mul_assoc]
    have ht' : (U.val*D).trace =
        (1/2 : ℂ) • ((U.val*Q*X).trace+(Q*U.val*X).trace) -
          (U.val*K).trace := by
      rw [hid, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_add,
        Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add, hc]
      simp only [Matrix.mul_assoc]
    rw [← hU, ht']
    norm_num [smul_eq_mul, Complex.mul_re]
  have h3' : -(U.val*K).trace.re ≤
      (b)*traceNorm X := by
    have hz : -(U.val*K).trace.re ≤
        traceNorm K := by
      simpa only [Unitary.coe_neg, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re] using h3
    exact hz.trans hk
  rw [heq]
  linarith


set_option maxHeartbeats 800000 in
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
  have hH (j : J) : (H j).IsHermitian := by
    apply (LinearMap.isHermitian_toMatrix_iff v).mpr
    intro x y
    change (∑ r, inner ℂ (h j (x r)) (y r)) = ∑ r, inner ℂ (x r) (h j (y r))
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
    have hz := ht n X
    change traceNorm (∑ j,
      LinearMap.toMatrix v.toBasis v.toBasis (referenceLift n (L j)) * X *
        (LinearMap.toMatrix v.toBasis v.toBasis (referenceLift n (L j)))ᴴ)
        ≤ (5*δ)*traceNorm X at hz
    have hm : (∑ j,
        LinearMap.toMatrix v.toBasis v.toBasis (referenceLift n (L j)) * X *
          (LinearMap.toMatrix v.toBasis v.toBasis (referenceLift n (L j)))ᴴ) =
        ∑ j, M j * X * (M j)ᴴ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hM]
    rwa [hm] at hz
  intro X
  have hid : X - ∑ j, H j * X * (H j)ᴴ =
      (1/2 : ℂ) • (Q*X+X*Q) - ∑ j, M j * X * (M j)ᴴ :=
    centered_defect_identity H hH hsum c X
  refine ⟨hid, ?_⟩
  simpa only [show (2:ℝ)*(5*δ)=10*δ by ring] using
    trace_centered_defect Q X (∑ j, M j * X * (M j)ᴴ)
      (X - ∑ j, H j * X * (H j)ᴴ) (5*δ) hqnorm (hk X) hid

end Hilbert

section Pinching
variable {a I J : Type*} [Fintype a] [DecidableEq a]
  [Fintype I] [Fintype J]

/-- Actual center pinching, represented on the whole ambient Hilbert space. -/
def centerPinching (P : I → Matrix a a ℂ) (X : Matrix a a ℂ) : Matrix a a ℂ :=
  ∑ i, P i * X * P i

private lemma kraus_trace_pairing (H : J → Matrix a a ℂ) (X Y : Matrix a a ℂ) :
    ((∑ j, H j*X*(H j)ᴴ)*Y).trace = (X*(∑ j, (H j)ᴴ*Y*H j)).trace := by
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (H j)]
  simp only [Matrix.mul_assoc]

private lemma pinch_id (P : I → Matrix a a ℂ)
    (hPP : ∀ i, P i * P i = P i) (hP : ∑ i, P i = 1)
    (X : Matrix a a ℂ) (hX : ∀ i, P i * X = X * P i) :
    centerPinching P X = X := by
  calc
    _ = ∑ i, X * P i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hX, Matrix.mul_assoc, hPP]
    _ = X := by rw [← Finset.mul_sum, hP, Matrix.mul_one]

private lemma pinch_kraus (P : I → Matrix a a ℂ)
    (hp : ∀ i, (P i)ᴴ = P i) (H : J → Matrix a a ℂ)
    (X : Matrix a a ℂ) (hX : centerPinching P X = X) :
    (∑ t : J × I × I,
      (P t.2.2 * H t.1 * P t.2.1) * X *
        (P t.2.2 * H t.1 * P t.2.1)ᴴ) =
      centerPinching P (∑ j, H j * X * (H j)ᴴ) := by
  classical
  simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul, hp]
  calc
    _ = ∑ j, ∑ k, ∑ i,
        (P k * H j * P i) * X * (P i * ((H j)ᴴ * P k)) := by
      exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = ∑ k, ∑ j, ∑ i,
        (P k * H j * P i) * X * (P i * ((H j)ᴴ * P k)) := Finset.sum_comm
    _ = ∑ k, ∑ j, P k * (H j * centerPinching P X * (H j)ᴴ) * P k := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      simp only [centerPinching, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [hX]
      simp only [centerPinching, Matrix.mul_sum, Matrix.sum_mul]

private lemma pinch_gram (P : I → Matrix a a ℂ)
    (hp : ∀ i, (P i)ᴴ = P i) (hpp : ∀ i, P i * P i = P i)
    (hs : ∑ i, P i = 1) (H : J → Matrix a a ℂ) :
    (∑ t : J × I × I,
      (P t.2.2 * H t.1 * P t.2.1)ᴴ * (P t.2.2 * H t.1 * P t.2.1)) =
      centerPinching P (∑ j, (H j)ᴴ * H j) := by
  classical
  simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul, hp]
  have hk (j : J) (i : I) :
      (∑ k, P i * ((H j)ᴴ * P k) * (P k * H j * P i)) =
        P i * ((H j)ᴴ * H j) * P i := by
    calc
      _ = ∑ k, P i * (H j)ᴴ * (P k * P k) * H j * P i := by
        simp only [Matrix.mul_assoc]
      _ = P i * (H j)ᴴ * (∑ k, P k) * H j * P i := by
        simp only [hpp, Matrix.mul_sum, Matrix.sum_mul]
      _ = _ := by rw [hs, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp_rw [hk]
  rw [Finset.sum_comm]
  simp only [centerPinching, Matrix.mul_sum, Matrix.sum_mul]

private lemma pinched_centered_identity (P : I → Matrix a a ℂ)
    (hpp : ∀ i, P i * P i = P i) (hsP : ∑ i, P i = 1)
    (H : J → Matrix a a ℂ)
    (hsH : ∑ j, H j * H j = 1) (c : J → I → ℝ)
    (X : Matrix a a ℂ) (hX : ∀ i, P i * X = X * P i)
    (C : J → Matrix a a ℂ)
    (hCl : ∀ j i, P i * C j = (c j i : ℂ) • P i)
    (hCr : ∀ j i, C j * P i = (c j i : ℂ) • P i) :
    let M := fun j => H j - C j
    let Q := centerPinching P (∑ j, M j * M j)
    X - centerPinching P (∑ j, H j * X * H j) =
      (1/2 : ℂ) • (Q*X+X*Q) - centerPinching P (∑ j, M j * X * M j) := by
  classical
  dsimp only
  have hm (j : J) (i : I) :
      (P i * (H j-C j) * (H j-C j) * P i)*X +
        X*(P i * (H j-C j) * (H j-C j) * P i) -
        (2 : ℂ) • (P i * (H j-C j)*X*(H j-C j)*P i) =
      (P i * H j * H j * P i)*X+X*(P i * H j * H j * P i) -
        (2 : ℂ) • (P i * H j * X * H j * P i) := by
    have hl : P i * (H j-C j) = P i * H j - (c j i : ℂ) • P i := by
      rw [Matrix.mul_sub, hCl]
    have hr : (H j-C j) * P i = H j * P i - (c j i : ℂ) • P i := by
      rw [Matrix.sub_mul, hCr]
    have hq : P i * (H j-C j) * (H j-C j) * P i =
        (P i * H j - (c j i : ℂ) • P i) *
          (H j * P i - (c j i : ℂ) • P i) := by
      rw [Matrix.mul_assoc (P i * (H j-C j)), hl, hr]
    have hk : P i * (H j-C j)*X*(H j-C j)*P i =
        (P i * H j - (c j i : ℂ) • P i)*X*
          (H j * P i - (c j i : ℂ) • P i) := by
      rw [Matrix.mul_assoc (P i * (H j-C j)*X), hl, hr]
    rw [hq, hk]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Algebra.smul_mul_assoc (R := ℂ),
      Algebra.mul_smul_comm (R := ℂ), hpp]
    have h1 : P i * H j * (P i * X) = P i * H j * (X * P i) := by rw [hX]
    have h2 : P i * X * (H j * P i) = X * (P i * (H j * P i)) := by
      rw [hX]; simp only [Matrix.mul_assoc]
    have h3 : P i * X * P i = P i * X := by
      rw [hX, Matrix.mul_assoc, hpp, ← hX]
    simp only [Matrix.mul_assoc] at h1 h2 h3 ⊢
    rw [← h1, h2, h3]
    simp only [hX i]
    module
  have ht := congrArg (fun f : J → I → Matrix a a ℂ => ∑ j, ∑ i, f j i)
    (funext (fun j => funext (hm j)))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum] at ht
  have hsum2 (Y Z : J → Matrix a a ℂ) :
      (∑ j, ∑ i, P i * Y j * Z j * P i) =
        centerPinching P (∑ j, Y j * Z j) := by
    rw [Finset.sum_comm]
    simp only [centerPinching, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  have hsum3 (Y Z : J → Matrix a a ℂ) :
      (∑ j, ∑ i, P i * Y j * X * Z j * P i) =
        centerPinching P (∑ j, Y j * X * Z j) := by
    rw [Finset.sum_comm]
    simp only [centerPinching, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  simp only [hsum2, hsum3] at ht
  have hI : centerPinching P (1 : Matrix a a ℂ) = 1 := by
    simp only [centerPinching, Matrix.mul_one, hpp, hsP]
  rw [hsH, hI, Matrix.one_mul, Matrix.mul_one] at ht
  calc
    _ = (1/2 : ℂ) • (X+X-(2 : ℂ) • centerPinching P (∑ j, H j*X*H j)) := by module
    _ = (1/2 : ℂ) •
        ((centerPinching P (∑ j, (H j-C j)*(H j-C j)))*X+
          X*(centerPinching P (∑ j, (H j-C j)*(H j-C j))) -
            (2 : ℂ) • centerPinching P (∑ j, (H j-C j)*X*(H j-C j))) :=
      congrArg (fun Z : Matrix a a ℂ => (1/2 : ℂ) • Z) ht.symm
    _ = _ := by module

end Pinching

section ActualDirectSum
open D5.S3.Quantum.Matrix.UniformVarianceCentering
open scoped MatrixOrder
variable {I : Type*} [Fintype I] [DecidableEq I]
  {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)]

set_option maxHeartbeats 4000000 in
-- Dependent block and reference coordinates require extended elaboration.
/-- The actual center-pinched channel and centered Kraus family have the global
complete-reference defect bound, from variance only inside each input block. -/
theorem hermitian_unital_direct_sum_defect_trace_bound {J : Type*} [Fintype J]
    (h : J → PiLp 2 E →ₗ[ℂ] PiLp 2 E) (hh : ∀ j, (h j).IsSymmetric)
    (hs : ∑ j, (h j).comp (h j) = LinearMap.id)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ i (x : E i), ‖x‖ = 1 →
      ∑ j, ‖h j (blockInclusion i x) -
        (inner ℂ (blockInclusion i x) (h j (blockInclusion i x))).re •
          blockInclusion i x‖^2 ≤ δ)
    (e : ∀ i, E i) (he : ∀ i, (∃ x : E i, ‖x‖ = 1) → ‖e i‖ = 1) :
    ∀ n : ℕ,
      let v := stdOrthonormalBasis ℂ (PiLp 2 (fun _ : Fin n => PiLp 2 E))
      let P := fun i => LinearMap.toMatrix v.toBasis v.toBasis
        (directSumReference n (blockProjection (E := E) i))
      let H := fun j => LinearMap.toMatrix v.toBasis v.toBasis (directSumReference n (h j))
      let M := fun j => LinearMap.toMatrix v.toBasis v.toBasis
        (directSumReference n (h j - centralMean h e j))
      let Q := centerPinching P (∑ j, M j * M j)
      let A := fun t : J × I × I => P t.2.2 * H t.1 * P t.2.1
      let B := fun t : J × I × I => P t.2.2 * M t.1 * P t.2.1
      Q ≤ (5*δ : ℝ) • 1 ∧
      (∑ t, (A t)ᴴ * A t = 1) ∧
      (∑ t, (B t)ᴴ * B t = Q) ∧
      (∀ Y, (centerPinching P Y).trace = Y.trace) ∧
      (∀ Y i, P i * centerPinching P Y = centerPinching P Y * P i) ∧
      (∀ X, (∀ i, P i * X = X * P i) →
        let K := centerPinching P (∑ j, M j * X * M j)
        let Phi := centerPinching P (∑ j, H j * X * H j)
        (K = ∑ t, B t * X * (B t)ᴴ) ∧
        (Phi = ∑ t, A t * X * (A t)ᴴ) ∧
        (X - Phi = (1/2 : ℂ) • (Q*X+X*Q) - K) ∧
        (traceNorm (X-Phi) ≤ min 2 (10*δ) * traceNorm X) ∧
        (Phi.trace = X.trace) ∧ (0 ≤ X → 0 ≤ Phi) ∧ (0 ≤ X → 0 ≤ K) ∧
        (∀ Y, (K*Y).trace = (X*(∑ t, (B t)ᴴ * Y * B t)).trace)) := by
  classical
  have hp := hermitian_direct_sum_centering h hh δ hδ hv e he
  intro n
  let U := PiLp 2 (fun _ : Fin n => PiLp 2 E)
  let v := stdOrthonormalBasis ℂ U
  let rP := fun i => directSumReference n (blockProjection (E := E) i)
  let P := fun i => LinearMap.toMatrix v.toBasis v.toBasis (rP i)
  let H := fun j => LinearMap.toMatrix v.toBasis v.toBasis (directSumReference n (h j))
  let C := fun j => LinearMap.toMatrix v.toBasis v.toBasis
    (directSumReference n (centralMean h e j))
  let M := fun j => LinearMap.toMatrix v.toBasis v.toBasis
    (directSumReference n (h j - centralMean h e j))
  let Q := centerPinching P (∑ j, M j * M j)
  let A := fun t : J × I × I => P t.2.2 * H t.1 * P t.2.1
  let B := fun t : J × I × I => P t.2.2 * M t.1 * P t.2.1
  have hrP (i : I) (x : U) (r : Fin n) :
      rP i x r = PiLp.single 2 i (x r i) := rfl
  have hrPs (i : I) : (rP i).IsSymmetric := by
    intro x y
    simp only [PiLp.inner_apply, hrP]
    apply Finset.sum_congr rfl
    intro r _
    have hl : inner ℂ (PiLp.single 2 i (x r i)) (y r) = inner ℂ (x r i) (y r i) := by
      rw [PiLp.inner_apply, Finset.sum_eq_single i]
      · simp
      · intro k _ hki; simp [hki]
      · simp
    have hr : inner ℂ (x r) (PiLp.single 2 i (y r i)) = inner ℂ (x r i) (y r i) := by
      rw [PiLp.inner_apply, Finset.sum_eq_single i]
      · simp
      · intro k _ hki; simp [hki]
      · simp
    exact hl.trans hr.symm
  have hP (i : I) : (P i)ᴴ = P i :=
    ((LinearMap.isHermitian_toMatrix_iff v).mpr (hrPs i)).eq
  have hcomp (i k : I) : (rP i).comp (rP k) = if i=k then rP i else 0 := by
    by_cases hik : i=k
    · subst k
      rw [if_pos rfl]
      apply LinearMap.ext
      intro x
      apply PiLp.ext
      intro r
      change PiLp.single 2 i ((PiLp.single 2 i (x r i)) i) = PiLp.single 2 i (x r i)
      simp
    · rw [if_neg hik]
      apply LinearMap.ext
      intro x
      apply PiLp.ext
      intro r
      change PiLp.single 2 i ((PiLp.single 2 k (x r k)) i) = 0
      simp [hik]
  have hPP (i k : I) : P i * P k = if i=k then P i else 0 := by
    have hz := congrArg (LinearMap.toMatrix v.toBasis v.toBasis) (hcomp i k)
    split_ifs at hz ⊢ with hik
    · simpa only [LinearMap.toMatrix_comp v.toBasis v.toBasis v.toBasis] using hz
    · simpa only [LinearMap.toMatrix_comp v.toBasis v.toBasis v.toBasis, map_zero] using hz
  have hpp (i : I) : P i * P i = P i := by simpa using hPP i i
  have hsumP : ∑ i, rP i = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro r
    simp only [LinearMap.sum_apply, LinearMap.id_apply, WithLp.ofLp_sum, Finset.sum_apply]
    change (∑ k, PiLp.single 2 k (x r k)) = x r
    apply WithLp.ofLp_injective
    simp only [WithLp.ofLp_sum]
    exact Finset.univ_sum_single (x r).ofLp
  have hsP : ∑ i, P i = 1 := by
    have hz := congrArg (LinearMap.toMatrix v.toBasis v.toBasis) hsumP
    simpa only [map_sum, LinearMap.toMatrix_id] using hz
  have hH (j : J) : (H j)ᴴ = H j := by
    apply ((LinearMap.isHermitian_toMatrix_iff v).mpr ?_).eq
    intro x y
    change (∑ r, inner ℂ (h j (x r)) (y r)) = ∑ r, inner ℂ (x r) (h j (y r))
    exact Finset.sum_congr rfl (fun r _ => hh j (x r) (y r))
  have hsH : ∑ j, H j * H j = 1 := by
    have hl : ∑ j, (directSumReference n (h j)).comp (directSumReference n (h j)) =
        LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply PiLp.ext
      intro r
      simp only [LinearMap.sum_apply, LinearMap.id_apply, WithLp.ofLp_sum, Finset.sum_apply]
      change (∑ j, h j (h j (x r))) = x r
      have hz := congrArg (fun T : PiLp 2 E →ₗ[ℂ] PiLp 2 E => T (x r)) hs
      simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] using hz
    have hz := congrArg (LinearMap.toMatrix v.toBasis v.toBasis) hl
    simpa only [map_sum, LinearMap.toMatrix_id,
      LinearMap.toMatrix_comp v.toBasis v.toBasis v.toBasis] using hz
  let c := fun j i => (inner ℂ (blockInclusion i (e i))
    (h j (blockInclusion i (e i)))).re
  have hC (j : J) : C j = ∑ i, (c j i : ℂ) • P i := by
    have hz : directSumReference n (centralMean h e j) =
        ∑ i, (c j i : ℂ) • rP i := by
      apply LinearMap.ext
      intro x
      apply PiLp.ext
      intro r
      change (centralMean h e j) (x r) = (∑ i, (c j i : ℂ) • rP i) x r
      simp only [centralMean, LinearMap.sum_apply, LinearMap.smul_apply,
        WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul]
      rfl
    change LinearMap.toMatrix v.toBasis v.toBasis _ = _
    rw [hz, map_sum]
    simp only [map_smul, P]
  have hCl (j : J) (i : I) : P i * C j = (c j i : ℂ) • P i := by
    rw [hC, Matrix.mul_sum]
    simp only [Matrix.mul_smul, hPP]
    simp
  have hCr (j : J) (i : I) : C j * P i = (c j i : ℂ) • P i := by
    rw [hC, Matrix.sum_mul]
    simp only [Matrix.smul_mul, hPP]
    simp
  have hCh (j : J) : (C j)ᴴ = C j := by
    rw [hC]
    simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hP]
  have hMdef (j : J) : M j = H j-C j := by
    have hz : directSumReference n (h j-centralMean h e j) =
        directSumReference n (h j) - directSumReference n (centralMean h e j) := by
      ext x r; rfl
    change LinearMap.toMatrix v.toBasis v.toBasis _ = _
    rw [hz, map_sub]
  have hM (j : J) : (M j)ᴴ = M j := by
    rw [hMdef, Matrix.conjTranspose_sub, hH, hCh]
  have hgB : ∑ t, (B t)ᴴ * B t = Q := by
    have hz := pinch_gram P hP hpp hsP M
    simpa only [hM] using hz
  have hgA : ∑ t, (A t)ᴴ * A t = 1 := by
    have hz := pinch_gram P hP hpp hsP H
    simpa only [hH, hsH, centerPinching, Matrix.mul_one, hpp, hsP] using hz
  let bL := fun t : J × I × I => (rP t.2.2).comp
    ((directSumReference n (h t.1-centralMean h e t.1)).comp (rP t.2.1))
  have hbmat (t : J × I × I) : LinearMap.toMatrix v.toBasis v.toBasis (bL t) = B t := by
    simp only [bL, B, LinearMap.toMatrix_comp v.toBasis v.toBasis v.toBasis,
      P, H, M, Matrix.mul_assoc]
  have hbadj (T : U →L[ℂ] U) :
      ‖(∑ t, (bL t).adjoint.comp (T.toLinearMap.comp (bL t))).toContinuousLinearMap‖
        ≤ (5*δ)*‖T‖ := (hp n).2 T
  have hK (X) : traceNorm (∑ t, B t * X * (B t)ᴴ) ≤ (5*δ)*traceNorm X := by
    have hz := kraus_trace_bound v v bL (5*δ) (by positivity) hbadj X
    simpa only [hbmat] using hz
  have hqmap : operator v Q =
      (∑ t, (bL t).adjoint.comp (bL t)).toContinuousLinearMap := by
    rw [← hgB]
    change (Matrix.toLin v.toBasis v.toBasis _).toContinuousLinearMap = _
    congr 1
    simp only [map_sum, Matrix.toLin_mul v.toBasis v.toBasis v.toBasis,
      ← hbmat, Matrix.toLin_conjTranspose, Matrix.toLin_toMatrix]
  have hqnorm : ‖Q‖ ≤ 5*δ := by
    have hz := hbadj (ContinuousLinearMap.id ℂ U)
    change ‖(∑ t, (bL t).adjoint.comp (bL t)).toContinuousLinearMap‖ ≤
      (5*δ)*‖ContinuousLinearMap.id ℂ U‖ at hz
    rw [← hqmap, StarAlgEquiv.norm_map (operator v) Q] at hz
    exact hz.trans (by nlinarith [ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := U)])
  have hQpos : 0 ≤ Q := by
    rw [← hgB]
    exact Finset.sum_nonneg (fun t _ => by
      change 0 ≤ star (B t) * B t
      exact star_mul_self_nonneg _)
  have hQle : Q ≤ (5*δ : ℝ) • 1 := by
    have hz := (CStarAlgebra.norm_le_iff_le_algebraMap Q (by positivity) hQpos).mp hqnorm
    simpa only [Algebra.algebraMap_eq_smul_one] using hz
  have hchannel (X) : traceNorm (∑ t, A t * X * (A t)ᴴ) ≤ traceNorm X :=
    unital_kraus_trace_bound v A hgA X
  refine ⟨hQle, hgA, hgB, ?_, ?_, ?_⟩
  · intro Y
    calc
      _ = ∑ i, (Y*(P i*P i)).trace := by
        simp only [centerPinching, Matrix.trace_sum, Matrix.mul_assoc]
        apply Finset.sum_congr rfl
        intro i _
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (P i) (Y*P i)
      _ = Y.trace := by
        simp only [hpp, ← Matrix.trace_sum, ← Matrix.mul_sum, hsP, Matrix.mul_one]
  · intro Y i
    have hl : P i * centerPinching P Y = P i * Y * P i := by
      simp only [centerPinching, Matrix.mul_sum, ← Matrix.mul_assoc, hPP]
      simp
    have hr : centerPinching P Y * P i = P i * Y * P i := by
      simp only [centerPinching, Matrix.sum_mul, Matrix.mul_assoc, hPP]
      simp [Matrix.mul_assoc]
    exact hl.trans hr.symm
  · intro X hX
    have hpin := pinch_id P hpp hsP X hX
    have hk : centerPinching P (∑ j, M j*X*M j) = ∑ t, B t*X*(B t)ᴴ := by
      simpa only [hM] using (pinch_kraus P hP M X hpin).symm
    have hf : centerPinching P (∑ j, H j*X*H j) = ∑ t, A t*X*(A t)ᴴ := by
      simpa only [hH] using (pinch_kraus P hP H X hpin).symm
    have hid : X-centerPinching P (∑ j, H j*X*H j) =
        (1/2:ℂ) • (Q*X+X*Q)-centerPinching P (∑ j, M j*X*M j) := by
      have hz := pinched_centered_identity P hpp hsP H hsH c X hX C hCl hCr
      simpa only [← hMdef] using hz
    refine ⟨hk,hf,hid,?_,?_,?_,?_,?_⟩
    · have hb := trace_centered_defect Q X (centerPinching P (∑ j, M j*X*M j))
        (X-centerPinching P (∑ j, H j*X*H j)) (5*δ) hqnorm (by rw [hk]; exact hK X) hid
      have hc : traceNorm (X-centerPinching P (∑ j, H j*X*H j)) ≤ 2*traceNorm X := by
        calc
          _ ≤ traceNorm X + traceNorm (-centerPinching P (∑ j, H j*X*H j)) :=
            by
              simpa only [sub_eq_add_neg] using
                (traceNorm_add_le X (-centerPinching P (∑ j, H j*X*H j)))
          _ ≤ 2*traceNorm X := by
            rw [traceNorm_neg, hf]
            linarith [hchannel X]
      rw [min_mul_of_nonneg (2:ℝ) (10*δ) (traceNorm_nonneg X)]
      exact le_min hc (by nlinarith)
    · rw [hf]
      have hz := kraus_trace_pairing A X 1
      simpa only [Matrix.mul_one, hgA] using hz
    · intro hpos
      rw [hf]
      exact Finset.sum_nonneg (fun t _ => star_right_conjugate_nonneg hpos (A t))
    · intro hpos
      rw [hk]
      exact Finset.sum_nonneg (fun t _ => star_right_conjugate_nonneg hpos (B t))
    · intro Y
      rw [hk]
      exact kraus_trace_pairing B X Y

end ActualDirectSum

end D5.S3.Quantum.Matrix.UniformVarianceTraceBound
