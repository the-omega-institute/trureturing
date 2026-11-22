/- GID: D5/S3/Quantum/Recovery/BKMFlagRefinement
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMFlagRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Faithful classical flag refinement preserves the actual marginal and physical BKM defects. -/

import D5.S3.Quantum.Recovery.BKMDiagonalStability
import D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.LogExp

/-! # Faithful classical flag refinement preserves the actual marginal and physical BKM defects -/

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (omega continuous_mpow)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight trace_partialTraceRight)

open private omega_smul_reference from D5.S3.Quantum.Recovery.BKMDiagonalStability

namespace D5.S3.Quantum.Recovery.BKMFlagRefinement

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

abbrev joint (T : ι → Matrix n n ℂ) : Matrix (n × ι) (n × ι) ℂ :=
  Matrix.blockDiagonal T

abbrev marginal (T : ι → Matrix n n ℂ) : Matrix n n ℂ :=
  partialTraceRight (joint T)

def lift (K : Matrix n n ℂ) : Matrix (n × ι) (n × ι) ℂ :=
  K ⊗ₖ (1 : Matrix ι ι ℂ)

def comm (A K : Matrix n n ℂ) : Matrix n n ℂ := A * K - K * A

def logDefect (τ : Matrix (n × ι) (n × ι) ℂ) (K : Matrix n n ℂ) : ℝ :=
  let C := comm (CFC.log τ - lift (ι := ι) (CFC.log (partialTraceRight τ))) (lift (ι := ι) K)
  (τ * (Cᴴ * C)).trace.re

def bkmGap (τ : Matrix (n × ι) (n × ι) ℂ) (K : Matrix n n ℂ) : ℝ :=
  (K * omega (partialTraceRight τ) K).trace.re -
    (lift (ι := ι) K * omega τ (lift (ι := ι) K)).trace.re

def logBlockTerm (W T K : Matrix n n ℂ) : ℝ :=
  let C := comm (CFC.log T - CFC.log W) K
  (T * (Cᴴ * C)).trace.re

def bkmBlockTerm (T K : Matrix n n ℂ) : ℝ :=
  (K * omega T K).trace.re

omit [Fintype n] [DecidableEq n] in
theorem marginal_eq_sum (T : ι → Matrix n n ℂ) : marginal T = ∑ i, T i := by
  ext x y
  simp [partialTraceRight, Matrix.sum_apply, Matrix.blockDiagonal_apply_eq]

omit [Fintype n] [DecidableEq n] [Fintype ι] in
theorem lift_eq_joint (K : Matrix n n ℂ) :
    lift (ι := ι) K = joint (fun _ : ι => K) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases hij : i = j
  · subst j
    simp [lift]
  · simp [lift, Matrix.blockDiagonal_apply, hij]

/-- The real spectrum is the union of the actual block spectra. -/
theorem mem_spectrum_joint (T : ι → Matrix n n ℂ) (x : ℝ) :
    x ∈ spectrum ℝ (joint T) ↔ ∃ i, x ∈ spectrum ℝ (T i) := by
  classical
  let A : ι → Matrix n n ℂ := fun i => algebraMap ℝ (Matrix n n ℂ) x - T i
  have hA : joint A = algebraMap ℝ (Matrix (n × ι) (n × ι) ℂ) x - joint T := by
    change joint ((fun _ : ι => algebraMap ℝ (Matrix n n ℂ) x) - T) = _
    unfold joint
    rw [Matrix.blockDiagonal_sub]
    congr 1
    simp only [Algebra.algebraMap_eq_smul_one]
    exact (Matrix.blockDiagonal_smul x (1 : ι → Matrix n n ℂ)).trans
      (congrArg (x • ·) Matrix.blockDiagonal_one)
  rw [spectrum.mem_iff, ← hA, Matrix.isUnit_iff_isUnit_det, Matrix.det_blockDiagonal]
  simp only [spectrum.mem_iff]
  -- In ℂ the product is zero exactly when a factor is zero.
  simp only [isUnit_iff_ne_zero, not_not, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, A, Matrix.isUnit_iff_isUnit_det]

theorem joint_posDef (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef) :
    (joint T).PosDef := by
  have hH := Matrix.isHermitian_blockDiagonal_iff.mpr (fun i => (hT i).isHermitian)
  apply hH.posDef_iff_eigenvalues_pos.mpr
  intro k
  obtain ⟨i, hi⟩ := (mem_spectrum_joint T _).mp (hH.eigenvalues_mem_spectrum_real k)
  rw [(hT i).isHermitian.spectrum_real_eq_range_eigenvalues] at hi
  obtain ⟨j, hj⟩ := hi
  rw [← hj]
  exact (hT i).eigenvalues_pos j

/-- The star algebra embedding of the flag blocks, reindexed to retained space first. -/
private def blockHom : (ι → Matrix n n ℂ) →⋆ₐ[ℂ] Matrix (n × ι) (n × ι) ℂ := by
  let φ : (ι → Matrix n n ℂ) →ₐ[ℂ] Matrix (n × ι) (n × ι) ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ
      ((Equiv.sigmaEquivProd ι n).trans (Equiv.prodComm ι n))).toAlgHom.comp
        (D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition.blockDiagonalAlgHom
          (fun _ : ι => n))
  have he : Matrix.blockDiagonal = ⇑φ := by
    exact Matrix.blockDiagonal_inj.mp rfl
  exact
    { φ.toRingHom.copy Matrix.blockDiagonal he with
      commutes' := by
        intro z
        exact (congrFun he _).trans (φ.commutes z)
      map_star' := by
        intro A
        exact (Matrix.blockDiagonal_conjTranspose A).symm }

theorem cfc_joint (f : ℝ → ℝ) (T : ι → Matrix n n ℂ)
    (hT : ∀ i, (T i).IsHermitian) :
    cfc f (joint T) = joint (fun i => cfc f (T i)) := by
  let : ContinuousFunctionalCalculus ℝ (ι → Matrix n n ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hSA : IsSelfAdjoint T := Pi.isSelfAdjoint.mpr hT
  have hJ : IsSelfAdjoint (blockHom T) := hSA.map _
  have hf : ContinuousOn f (spectrum ℝ T) := by
    rw [Pi.spectrum_eq]
    exact (Set.finite_iUnion (fun i => (T i).finite_real_spectrum)).continuousOn _
  have hc : Continuous (blockHom (n := n) (ι := ι)) :=
    (blockHom (n := n) (ι := ι)).toLinearMap.continuous_of_finiteDimensional
  have hm := (blockHom (n := n) (ι := ι)).map_cfc f T hf hc hSA hJ
  rw [cfc_map_pi (S := ℂ) f T (by simpa only [Pi.spectrum_eq] using hf) hSA hT] at hm
  exact hm.symm

theorem mpow_joint (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).IsHermitian) (t : ℝ) :
    mpow (joint T) t = joint (fun i => mpow (T i) t) :=
  cfc_joint (fun x => x ^ t) T hT

private theorem integrable_bkm (A X : Matrix n n ℂ) (hA : A.PosDef) :
    IntervalIntegrable (fun t : ℝ => mpow A t * X * mpow A (1 - t)) volume 0 1 := by
  have ht : Continuous (fun t : ℝ => 1 - t) := continuous_const.sub continuous_id
  exact (((continuous_mpow A hA).mul continuous_const).mul
    ((continuous_mpow A hA).comp ht)).intervalIntegrable 0 1

theorem omega_joint (T X : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef) :
    omega (joint T) (joint X) = joint (fun i => omega (T i) (X i)) := by
  have hpoint (s : ℝ) :
      mpow (joint T) s * joint X * mpow (joint T) (1 - s) =
        joint (fun i => mpow (T i) s * X i * mpow (T i) (1 - s)) := by
    rw [mpow_joint T (fun i => (hT i).isHermitian),
      mpow_joint T (fun i => (hT i).isHermitian), ← Matrix.blockDiagonal_mul,
      ← Matrix.blockDiagonal_mul]
  ext ⟨x, i⟩ ⟨y, j⟩
  let E := (Matrix.entryLinearMap ℂ ℂ (x, i) (y, j)).toContinuousLinearMap
  change E (omega (joint T) (joint X)) = _
  rw [omega, ← E.intervalIntegral_comp_comm (integrable_bkm _ _ (joint_posDef T hT))]
  change (∫ s : ℝ in 0..1, (mpow (joint T) s * joint X * mpow (joint T) (1 - s))
    (x, i) (y, j)) = _
  simp_rw [hpoint]
  by_cases h : i = j
  · subst j
    let e := (Matrix.entryLinearMap ℂ ℂ x y).toContinuousLinearMap
    simp only [Matrix.blockDiagonal_apply_eq]
    change (∫ s : ℝ in 0..1, e (mpow (T i) s * X i * mpow (T i) (1 - s))) =
      e (omega (T i) (X i))
    rw [omega, e.intervalIntegral_comp_comm (integrable_bkm _ _ (hT i))]
  · simp [Matrix.blockDiagonal_apply, h]

theorem logDefect_joint (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (K : Matrix n n ℂ) :
    logDefect (joint T) K = ∑ i, logBlockTerm (marginal T) (T i) K := by
  unfold logDefect logBlockTerm CFC.log comm
  rw [cfc_joint _ T (fun i => (hT i).isHermitian)]
  simp only [lift_eq_joint, joint, ← Matrix.blockDiagonal_sub, ← Matrix.blockDiagonal_mul]
  rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
    ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal, Complex.re_sum]
  rfl

theorem bkmGap_joint (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (K : Matrix n n ℂ) :
    bkmGap (joint T) K =
      bkmBlockTerm (marginal T) K - ∑ i, bkmBlockTerm (T i) K := by
  unfold bkmGap bkmBlockTerm
  simp only [lift_eq_joint, omega_joint T _ hT, ← Matrix.blockDiagonal_mul,
    Matrix.trace_blockDiagonal, Complex.re_sum]

/-- The faithful case of the log scaling in HermitianMat.LogExp. -/
private theorem log_smul_faithful {T : Matrix n n ℂ} (hT : T.PosDef)
    {c : ℝ} (hc : 0 < c) :
    CFC.log (c • T) = Real.log c • (1 : Matrix n n ℂ) + CFC.log T := by
  have hzero (x : ℝ) (hx : x ∈ spectrum ℝ T) : x ≠ 0 := by
    rw [hT.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨j, rfl⟩ := hx
    exact (hT.eigenvalues_pos j).ne'
  have hsupport : cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) T = 1 := by
    rw [← cfc_const_one ℝ T]
    exact cfc_congr (fun x hx => by simp [hzero x hx])
  unfold CFC.log
  rw [hT.isHermitian.log_smul_of_ne_zero hc.ne', hsupport]

private theorem logBlockTerm_smul (W T K : Matrix n n ℂ) (hT : T.PosDef)
    {c : ℝ} (hc : 0 < c) :
    logBlockTerm W (c • T) K = c * logBlockTerm W T K := by
  have hcomm : comm (CFC.log (c • T) - CFC.log W) K = comm (CFC.log T - CFC.log W) K := by
    rw [log_smul_faithful hT hc, add_sub_assoc]
    simp only [comm, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    abel
  simp only [logBlockTerm, hcomm, Matrix.smul_mul, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul]

private theorem bkmBlockTerm_smul (T K : Matrix n n ℂ) (hT : T.PosDef)
    {c : ℝ} (hc : 0 < c) : bkmBlockTerm (c • T) K = c * bkmBlockTerm T K := by
  simp only [bkmBlockTerm, omega_smul_reference hT hc, Matrix.mul_smul,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

/-- A uniform split uses one child for each untouched parent. -/
abbrev UniformChild (split : ι) (m : ℕ) (i : ι) :=
  Fin (if i = split then m else 1)

def uniformWeight (split : ι) (m : ℕ) (i : ι) (_ : UniformChild split m i) : ℝ :=
  ((if i = split then m else 1 : ℕ) : ℝ)⁻¹

omit [Fintype ι] in
private theorem uniformWeight_pos (split : ι) {m : ℕ} (hm : 0 < m)
    (i : ι) (j : UniformChild split m i) : 0 < uniformWeight split m i j := by
  by_cases h : i = split <;> simp [uniformWeight, h, hm]

omit [Fintype ι] in
private theorem uniformWeight_sum (split : ι) {m : ℕ} (hm : 0 < m) (i : ι) :
    (∑ j : UniformChild split m i, uniformWeight split m i j) = 1 := by
  by_cases h : i = split
  · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [uniformWeight, UniformChild, h, hm0]
  · simp [uniformWeight, UniformChild, h]

section Weighted

variable {J : ι → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

def refinedBlocks (w : ∀ i, J i → ℝ) (T : ι → Matrix n n ℂ) :
    (Σ i, J i) → Matrix n n ℂ :=
  fun q => w q.1 q.2 • T q.1

def mergeBlocks (S : (Σ i, J i) → Matrix n n ℂ) (i : ι) : Matrix n n ℂ :=
  ∑ j : J i, S ⟨i, j⟩

omit [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (J i)] in
theorem merge_refinedBlocks (w : ∀ i, J i → ℝ) (hw : ∀ i, ∑ j, w i j = 1)
    (T : ι → Matrix n n ℂ) : mergeBlocks (refinedBlocks w T) = T := by
  funext i
  simp only [mergeBlocks, refinedBlocks, ← Finset.sum_smul, hw, one_smul]

omit [Fintype n] [DecidableEq n] in
theorem marginal_refined (w : ∀ i, J i → ℝ) (hw : ∀ i, ∑ j, w i j = 1)
    (T : ι → Matrix n n ℂ) :
    marginal (refinedBlocks w T) = marginal T := by
  rw [marginal_eq_sum, marginal_eq_sum, Fintype.sum_sigma]
  change (∑ i, mergeBlocks (refinedBlocks w T) i) = _
  rw [merge_refinedBlocks w hw]

omit [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)] in
theorem refinedBlocks_posDef (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j)
    (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef) :
    ∀ q, (refinedBlocks w T q).PosDef :=
  fun q => (hT q.1).smul (hw q.1 q.2)

omit [DecidableEq ι] [∀ i, DecidableEq (J i)] in
private theorem sum_weighted (w : ∀ i, J i → ℝ) (hw : ∀ i, ∑ j, w i j = 1)
    (f : ι → ℝ) : (∑ q : Σ i, J i, w q.1 q.2 * f q.1) = ∑ i, f i := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j : J i, w i j * f i) = f i
  rw [← Finset.sum_mul, hw, one_mul]

/-- Exact equalities of the physical defects for normalized positive refinements. -/
theorem refine_defects (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1)
    (K : Matrix n n ℂ) :
    logDefect (joint (refinedBlocks w T)) K = logDefect (joint T) K ∧
    bkmGap (joint (refinedBlocks w T)) K = bkmGap (joint T) K := by
  have hR := refinedBlocks_posDef w hw T hT
  constructor
  · rw [logDefect_joint _ hR, logDefect_joint _ hT, marginal_refined w hs]
    simp only [refinedBlocks, logBlockTerm_smul _ _ _ (hT _) (hw _ _)]
    exact sum_weighted w hs (fun i => logBlockTerm (marginal T) (T i) K)
  · rw [bkmGap_joint _ hR, bkmGap_joint _ hT, marginal_refined w hs]
    congr 1
    simp only [refinedBlocks, bkmBlockTerm_smul _ _ (hT _) (hw _ _)]
    exact sum_weighted w hs (fun i => bkmBlockTerm (T i) K)

/-- The joint references and their actual common marginal are faithful trace-one
matrices. Both defects refer to the same retained Hermitian observable. -/
theorem physical_refinement [Nonempty ι] (T : ι → Matrix n n ℂ)
    (hT : ∀ i, (T i).PosDef) (htr : (joint T).trace = 1)
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1)
    (K : Matrix n n ℂ) (hK : K.IsHermitian) :
    (joint T).PosDef ∧ (joint (refinedBlocks w T)).PosDef ∧
    (joint (refinedBlocks w T)).trace = 1 ∧ (marginal T).PosDef ∧
    (marginal T).trace = 1 ∧ marginal (refinedBlocks w T) = marginal T ∧
    (lift (ι := ι) K).IsHermitian ∧ (lift (ι := Σ i, J i) K).IsHermitian ∧
    logDefect (joint (refinedBlocks w T)) K = logDefect (joint T) K ∧
    bkmGap (joint (refinedBlocks w T)) K = bkmGap (joint T) K := by
  have hMarg := marginal_refined w hs T
  have hTrace : (marginal T).trace = 1 := (trace_partialTraceRight _).trans htr
  have hTrace' : (joint (refinedBlocks w T)).trace = 1 :=
    (trace_partialTraceRight _).symm.trans ((congrArg Matrix.trace hMarg).trans hTrace)
  have hPos : (marginal T).PosDef := by
    rw [marginal_eq_sum]
    exact Matrix.posDef_sum Finset.univ_nonempty (fun i _ => hT i)
  refine ⟨joint_posDef T hT, joint_posDef _ (refinedBlocks_posDef w hw T hT),
    hTrace', hPos, hTrace, hMarg, ?_, ?_, refine_defects T hT w hw hs K⟩
  · rw [lift_eq_joint]
    exact Matrix.isHermitian_blockDiagonal_iff.mpr fun _ => hK
  · rw [lift_eq_joint]
    exact Matrix.isHermitian_blockDiagonal_iff.mpr fun _ => hK

theorem refine_positive_gap_and_ratio (T : ι → Matrix n n ℂ)
    (hT : ∀ i, (T i).PosDef) (w : ∀ i, J i → ℝ)
    (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1)
    (K : Matrix n n ℂ) (hG : 0 < bkmGap (joint T) K) :
    0 < bkmGap (joint (refinedBlocks w T)) K ∧
    logDefect (joint (refinedBlocks w T)) K / bkmGap (joint (refinedBlocks w T)) K =
      logDefect (joint T) K / bkmGap (joint T) K := by
  obtain ⟨hM, hG'⟩ := refine_defects T hT w hw hs K
  rw [hM, hG']
  exact ⟨hG, rfl⟩

end Weighted

abbrev uniformBlocks (T : ι → Matrix n n ℂ) (split : ι) (m : ℕ) :=
  refinedBlocks (uniformWeight split m) T

theorem uniform_refinement (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (split : ι) {m : ℕ} (hm : 0 < m) (K : Matrix n n ℂ) :
    marginal (uniformBlocks T split m) = marginal T ∧
    logDefect (joint (uniformBlocks T split m)) K = logDefect (joint T) K ∧
    bkmGap (joint (uniformBlocks T split m)) K = bkmGap (joint T) K := by
  exact ⟨marginal_refined _ (uniformWeight_sum split hm) T,
    refine_defects T hT _ (uniformWeight_pos split hm) (uniformWeight_sum split hm) K⟩

end D5.S3.Quantum.Recovery.BKMFlagRefinement
