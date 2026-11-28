/- GID: D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.claim; result=D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.result; claim=D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.claim
   digest: A faithful two-flag qutrit refutes the conditional Gibbs root-fidelity bound. -/

import D5.S3.Quantum.CommutingMidpoint.Fidelity
import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Recovery.BKMRelativeDensity
import D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritFirstFlag
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-! A faithful two-flag qutrit counterexample to the ordinary-Petz root-fidelity
lower bound for the normalized conditional Gibbs state. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritPhysicalRefutation

open _root_.Matrix
open scoped BigOperators ComplexOrder Kronecker _root_.Matrix MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.CommutingMidpoint (rootFidelity)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm re_trace_eq_trace traceNorm_eq_max_re_tr_U)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight trace_partialTraceRight)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (mpow_smul_of_nonneg)

section FlagBlocks

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

private abbrev joint (T : ι → Matrix n n ℂ) : Matrix (n × ι) (n × ι) ℂ :=
  Matrix.blockDiagonal T

private abbrev marginal (T : ι → Matrix n n ℂ) : Matrix n n ℂ :=
  partialTraceRight (joint T)

private def lift (K : Matrix n n ℂ) : Matrix (n × ι) (n × ι) ℂ :=
  K ⊗ₖ (1 : Matrix ι ι ℂ)

omit [Fintype n] [DecidableEq n] in
private theorem marginal_eq_sum (T : ι → Matrix n n ℂ) : marginal T = ∑ i, T i := by
  ext x y
  simp [partialTraceRight, Matrix.sum_apply, Matrix.blockDiagonal_apply_eq]

omit [Fintype n] [DecidableEq n] [Fintype ι] in
private theorem lift_eq_joint (K : Matrix n n ℂ) :
    lift (ι := ι) K = joint (fun _ : ι => K) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases hij : i = j
  · subst j
    simp [lift]
  · simp [lift, Matrix.blockDiagonal_apply, hij]

/-- The real spectrum is the union of the actual block spectra. -/
private theorem mem_spectrum_joint (T : ι → Matrix n n ℂ) (x : ℝ) :
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

private theorem joint_posDef (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef) :
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

private theorem cfc_joint (f : ℝ → ℝ) (T : ι → Matrix n n ℂ)
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

private theorem mpow_joint (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).IsHermitian) (t : ℝ) :
    mpow (joint T) t = joint (fun i => mpow (T i) t) :=
  cfc_joint (fun x => x ^ t) T hT

omit [DecidableEq n] in
private theorem traceNorm_joint (S : ι → Matrix n n ℂ) :
    traceNorm (joint S) = ∑ i, traceNorm (S i) := by
  classical
  let Q : ι → Matrix n n ℂ := fun i => (S i)ᴴ * S i
  have hQ (i : ι) : (Q i).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have hgram : (joint S)ᴴ * joint S = joint Q := by
    simp only [joint, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    rfl
  simp only [Foundation.FiniteTraceDistance.traceNorm, hgram]
  rw [CFC.sqrt_eq_real_sqrt _ (hgram ▸ (Matrix.posSemidef_conjTranspose_mul_self _).nonneg),
    cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := Real.sqrt_zero),
    cfc_joint _ Q (fun i => (hQ i).isHermitian), Matrix.trace_blockDiagonal, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [CFC.sqrt_eq_real_sqrt _ (hQ i).nonneg,
      cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := Real.sqrt_zero)]

-- Adjoint invariance follows from the unitary variational formula for the trace norm.
private theorem traceNorm_conjTranspose (A : Matrix n n ℂ) :
    traceNorm Aᴴ = traceNorm A := by
  have hle (X : Matrix n n ℂ) : traceNorm Xᴴ ≤ traceNorm X := by
    obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U Xᴴ).1
    apply (traceNorm_eq_max_re_tr_U X).2
    refine ⟨star U, ?_⟩
    change (U.valᴴ * X).trace.re = traceNorm Xᴴ
    calc
      _ = (X * U.valᴴ).trace.re := congrArg Complex.re (Matrix.trace_mul_comm _ _)
      _ = ((U.val * Xᴴ)ᴴ).trace.re := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = (U.val * Xᴴ).trace.re := by
        rw [Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
      _ = _ := hU
  exact le_antisymm (hle A) (by simpa only [Matrix.conjTranspose_conjTranspose] using hle Aᴴ)

-- The trace adjoint of the right partial trace tensors with the flag identity.
private def partialTracePetz (τ : Matrix (n × ι) (n × ι) ℂ) (X : Matrix n n ℂ) :
    Matrix (n × ι) (n × ι) ℂ :=
  let Q := mpow τ (1 / 2)
  let P := mpow (partialTraceRight τ) (-(1 / 2))
  Q * lift (ι := ι) (P * X * P) * Q

private def petzBlocks (T : ι → Matrix n n ℂ) (X : Matrix n n ℂ) (i : ι) : Matrix n n ℂ :=
  let Q := mpow (T i) (1 / 2)
  let P := mpow (marginal T) (-(1 / 2))
  Q * (P * X * P) * Q

private theorem partialTracePetz_joint (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (X : Matrix n n ℂ) :
    partialTracePetz (joint T) X = joint (petzBlocks T X) := by
  simp only [partialTracePetz, mpow_joint T (fun i => (hT i).isHermitian),
    lift_eq_joint, joint, ← Matrix.blockDiagonal_mul]
  rfl

end FlagBlocks

local notation "Qutrit" => Matrix (Fin 3) (Fin 3) ℂ
private abbrev Joint := Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ

private def mixedQutrit : Qutrit := (1 / 3 : ℝ) • (1 : Qutrit)

private def inputJoint (Q : Qutrit) : Joint :=
  joint (fun _ : Fin 2 => (1 / 2 : ℝ) • Q)

private def referenceBlocks (D : Fin 2 → Qutrit) (i : Fin 2) : Qutrit :=
  (1 / 3 : ℝ) • D i

private def referenceJoint (D : Fin 2 → Qutrit) : Joint := joint (referenceBlocks D)

private theorem input_marginal (Q : Qutrit) : partialTraceRight (inputJoint Q) = Q := by
  change marginal (fun _ : Fin 2 => (1 / 2 : ℝ) • Q) = Q
  rw [marginal_eq_sum, Fin.sum_univ_two, ← add_smul]
  norm_num

private theorem reference_marginal (D : Fin 2 → Qutrit) (hsum : ∑ i, D i = 1) :
    partialTraceRight (referenceJoint D) = mixedQutrit := by
  change marginal (referenceBlocks D) = _
  rw [marginal_eq_sum]
  change (∑ i, (1 / 3 : ℝ) • D i) = (1 / 3 : ℝ) • (1 : Qutrit)
  rw [← Finset.smul_sum, hsum]

private theorem input_faithful_density (Q : Qutrit) (hQ : Q.PosDef) (htr : Q.trace = 1) :
    (inputJoint Q).PosDef ∧ (inputJoint Q).trace = 1 := by
  refine ⟨joint_posDef _ (fun _ => hQ.smul (by norm_num : (0 : ℝ) < 1 / 2)), ?_⟩
  rw [← trace_partialTraceRight, input_marginal, htr]

private theorem referenceBlocks_posDef (D : Fin 2 → Qutrit)
    (hD : ∀ i, (D i).PosDef) (i : Fin 2) : (referenceBlocks D i).PosDef :=
  (hD i).smul (by norm_num : (0 : ℝ) < 1 / 3)

private theorem reference_faithful_density (D : Fin 2 → Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    (referenceJoint D).PosDef ∧ (referenceJoint D).trace = 1 := by
  refine ⟨joint_posDef _ (referenceBlocks_posDef D hD), ?_⟩
  rw [← trace_partialTraceRight, reference_marginal D hsum]
  norm_num [mixedQutrit, Matrix.trace_smul, Matrix.trace_one, Complex.real_smul]

private theorem mpow_half {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : 0 ≤ A) : mpow A (1 / 2) = CFC.sqrt A := by
  rw [mpow, CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hA]

private theorem sqrt_joint {n ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι] (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef) :
    CFC.sqrt (joint T) = joint (fun i => CFC.sqrt (T i)) := by
  rw [← mpow_half (joint_posDef T hT).posSemidef.nonneg,
    mpow_joint T (fun i => (hT i).isHermitian)]
  apply congrArg joint
  funext i
  exact mpow_half (hT i).posSemidef.nonneg

private theorem mpow_mixed (p : ℝ) :
    mpow mixedQutrit p = ((1 / 3 : ℝ) ^ p) • (1 : Qutrit) := by
  simp only [mixedQutrit, mpow, ← Algebra.algebraMap_eq_smul_one, cfc_algebraMap]

private def recoveredBlocks (D : Fin 2 → Qutrit) (Q : Qutrit) (i : Fin 2) : Qutrit :=
  CFC.sqrt (D i) * Q * CFC.sqrt (D i)

/-- Recovery by the ordinary Petz map applied to the actual partial trace of the input. -/
private theorem partialTracePetz_eq_joint (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    partialTracePetz (referenceJoint D) (partialTraceRight (inputJoint Q)) =
      joint (recoveredBlocks D Q) := by
  rw [input_marginal, referenceJoint, partialTracePetz_joint _ (referenceBlocks_posDef D hD)]
  apply congrArg joint
  funext i
  have hm : marginal (referenceBlocks D) = mixedQutrit := reference_marginal D hsum
  have hc : (0 : ℝ) < 1 / 3 := by norm_num
  have hroot := mpow_smul_of_nonneg (hD i).posSemidef.nonneg hc.le
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  change mpow ((1 / 3 : ℝ) • D i) (1 / 2) *
    (mpow (marginal (referenceBlocks D)) (-(1 / 2)) * Q *
      mpow (marginal (referenceBlocks D)) (-(1 / 2))) *
    mpow ((1 / 3 : ℝ) • D i) (1 / 2) = recoveredBlocks D Q i
  rw [hm, mpow_mixed, hroot, mpow_half (hD i).posSemidef.nonneg]
  let s : ℝ := (1 / 3 : ℝ) ^ (1 / 2 : ℝ)
  let t : ℝ := (1 / 3 : ℝ) ^ (-(1 / 2) : ℝ)
  let S : Qutrit := CFC.sqrt (D i)
  have hst : s * t = 1 := by
    dsimp only [s, t]
    rw [← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero]
  have hts : t * s = 1 := (mul_comm t s).trans hst
  have hleft : (s • S) * (t • (1 : Qutrit)) = S := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hst, one_smul]
  have hright : (t • (1 : Qutrit)) * (s • S) = S := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hts, one_smul]
  change (s • S) * ((t • (1 : Qutrit)) * Q * (t • (1 : Qutrit))) * (s • S) =
    S * Q * S
  calc
    _ = ((s • S) * (t • (1 : Qutrit))) * Q * ((t • (1 : Qutrit)) * (s • S)) := by
      simp only [Matrix.mul_assoc]
    _ = S * Q * S := by rw [hleft, hright]

private theorem recoveredBlocks_posDef (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hQ : Q.PosDef) (i : Fin 2) :
    (recoveredBlocks D Q i).PosDef := by
  have hS := (hD i).isStrictlyPositive.sqrt.posDef
  have h := (hS.isUnit.posDef_star_right_conjugate_iff).mpr hQ
  simpa only [recoveredBlocks, hS.isHermitian.star_eq] using h

private theorem recovered_faithful_density (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1)
    (hQ : Q.PosDef) (htr : Q.trace = 1) :
    let P := partialTracePetz (referenceJoint D) (partialTraceRight (inputJoint Q))
    P.PosDef ∧ P.trace = 1 := by
  dsimp only
  rw [partialTracePetz_eq_joint D Q hD hsum]
  refine ⟨joint_posDef _ (recoveredBlocks_posDef D Q hD hQ), ?_⟩
  have hblock (i : Fin 2) : (recoveredBlocks D Q i).trace = (Q * D i).trace := by
    rw [recoveredBlocks, Matrix.trace_mul_cycle,
      CFC.sqrt_mul_sqrt_self _ (hD i).posSemidef.nonneg, Matrix.trace_mul_comm (D i) Q]
  rw [Matrix.trace_blockDiagonal]
  simp_rw [hblock]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, hsum, Matrix.mul_one, htr]

/-- The unnormalized conditional Gibbs operator of the physical partial trace. -/
private def gibbsOperator (X T : Joint) : Joint :=
  NormedSpace.exp (CFC.log T +
    lift (CFC.log (partialTraceRight X) - CFC.log (partialTraceRight T)))

private def normalizedGibbs (X T : Joint) : Joint :=
  (gibbsOperator X T).trace.re⁻¹ • gibbsOperator X T

private def gibbsBlocks (D : Fin 2 → Qutrit) (Q : Qutrit) (i : Fin 2) : Qutrit :=
  NormedSpace.exp (CFC.log (D i) + CFC.log Q)

private def partition (D : Fin 2 → Qutrit) (Q : Qutrit) : ℝ :=
  ∑ i, (gibbsBlocks D Q i).trace.re

private theorem blockHamiltonian_hermitian (D : Fin 2 → Qutrit) (Q : Qutrit) (i : Fin 2) :
    (CFC.log (D i) + CFC.log Q).IsHermitian :=
  IsSelfAdjoint.log.add IsSelfAdjoint.log

private theorem gibbsBlocks_posDef (D : Fin 2 → Qutrit) (Q : Qutrit) (i : Fin 2) :
    (gibbsBlocks D Q i).PosDef := by
  unfold gibbsBlocks
  have hnonneg := (blockHamiltonian_hermitian D Q i).isSelfAdjoint.exp_nonneg
  exact hnonneg.posSemidef.posDef_iff_isUnit.mpr (Matrix.isUnit_exp _)

private theorem partition_pos (D : Fin 2 → Qutrit) (Q : Qutrit) : 0 < partition D Q := by
  exact Finset.sum_pos (fun i _ => (Complex.pos_iff.mp (gibbsBlocks_posDef D Q i).trace_pos).1)
    Finset.univ_nonempty

private theorem log_mixed :
    CFC.log mixedQutrit = algebraMap ℝ Qutrit (Real.log (1 / 3)) := by
  rw [mixedQutrit, ← Algebra.algebraMap_eq_smul_one, CFC.log_algebraMap]

private theorem gibbsOperator_eq_joint (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    gibbsOperator (inputJoint Q) (referenceJoint D) = joint (gibbsBlocks D Q) := by
  let H : Fin 2 → Qutrit := fun i => CFC.log (D i) + CFC.log Q
  have hH (i : Fin 2) : (H i).IsHermitian := blockHamiltonian_hermitian D Q i
  have hlog : CFC.log (referenceJoint D) =
      joint (fun i => CFC.log (referenceBlocks D i)) :=
    cfc_joint Real.log (referenceBlocks D) (fun i => (referenceBlocks_posDef D hD i).isHermitian)
  have hHamiltonian :
      CFC.log (referenceJoint D) + lift (CFC.log (partialTraceRight (inputJoint Q)) -
        CFC.log (partialTraceRight (referenceJoint D))) = joint H := by
    rw [input_marginal, reference_marginal D hsum, hlog, lift_eq_joint,
      ← Matrix.blockDiagonal_add]
    apply congrArg joint
    funext i
    change CFC.log ((1 / 3 : ℝ) • D i) +
      (CFC.log Q - CFC.log mixedQutrit) = CFC.log (D i) + CFC.log Q
    rw [CFC.log_smul' _ (by norm_num : (0 : ℝ) < 1 / 3) (hD i).isStrictlyPositive, log_mixed]
    abel
  have hJoint : (joint H).IsHermitian := Matrix.isHermitian_blockDiagonal_iff.mpr hH
  rw [gibbsOperator, hHamiltonian, ← CFC.real_exp_eq_normedSpace_exp hJoint.isSelfAdjoint,
    cfc_joint Real.exp H hH]
  apply congrArg joint
  funext i
  exact CFC.real_exp_eq_normedSpace_exp (hH i).isSelfAdjoint

private theorem gibbsOperator_trace (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    (gibbsOperator (inputJoint Q) (referenceJoint D)).trace.re = partition D Q := by
  rw [gibbsOperator_eq_joint D Q hD hsum, Matrix.trace_blockDiagonal,
    Complex.re_sum, partition]

private theorem normalizedGibbs_eq_scaledJoint (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    normalizedGibbs (inputJoint Q) (referenceJoint D) =
      (partition D Q)⁻¹ • joint (gibbsBlocks D Q) := by
  rw [normalizedGibbs, gibbsOperator_trace D Q hD hsum, gibbsOperator_eq_joint D Q hD hsum]

private theorem normalizedGibbs_faithful_density (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    let G := normalizedGibbs (inputJoint Q) (referenceJoint D)
    G.PosDef ∧ G.trace = 1 := by
  dsimp only
  rw [normalizedGibbs_eq_scaledJoint D Q hD hsum]
  have hG := joint_posDef _ (gibbsBlocks_posDef D Q)
  have hZ := partition_pos D Q
  refine ⟨hG.smul (inv_pos.mpr hZ), ?_⟩
  have hre : (joint (gibbsBlocks D Q)).trace.re = partition D Q := by
    rw [Matrix.trace_blockDiagonal, Complex.re_sum, partition]
  have hcast : (↑(partition D Q) : ℂ) = (joint (gibbsBlocks D Q)).trace := by
    rw [← hre]
    exact re_trace_eq_trace hG.isHermitian
  rw [Matrix.trace_smul, ← hcast, Complex.real_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hZ.ne', Complex.ofReal_one]

private def polarBlocks (D : Fin 2 → Qutrit) (Q : Qutrit) (i : Fin 2) : Qutrit :=
  CFC.sqrt (gibbsBlocks D Q i) * CFC.sqrt (D i) * CFC.sqrt Q

private theorem sqrt_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : 0 ≤ A) {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • A) = Real.sqrt c • CFC.sqrt A := by
  rw [← mpow_half (smul_nonneg hc hA), mpow_smul_of_nonneg hA hc (by norm_num),
    mpow_half hA, Real.sqrt_eq_rpow]

private theorem recovered_eq_polar_gram (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hQ : Q.PosDef) (i : Fin 2) :
    CFC.sqrt (gibbsBlocks D Q i) * recoveredBlocks D Q i *
        CFC.sqrt (gibbsBlocks D Q i) =
      polarBlocks D Q i * (polarBlocks D Q i)ᴴ := by
  let R := CFC.sqrt (gibbsBlocks D Q i)
  let S := CFC.sqrt (D i)
  let T := CFC.sqrt Q
  have root_star (A : Qutrit) : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hGram : (R * S * T) * (R * S * T)ᴴ = R * (S * Q * S) * R := by
    simp only [Matrix.conjTranspose_mul, R, S, T, root_star, Matrix.mul_assoc]
    change R * (S * (T * (T * (S * R)))) = R * (S * (Q * (S * R)))
    rw [← Matrix.mul_assoc T T, CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg]
  exact hGram.symm

private theorem rootFidelity_physical (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) (hQ : Q.PosDef) :
    rootFidelity (normalizedGibbs (inputJoint Q) (referenceJoint D))
      (partialTracePetz (referenceJoint D) (partialTraceRight (inputJoint Q))) =
      (∑ i, traceNorm (polarBlocks D Q i)) / Real.sqrt (partition D Q) := by
  have hG := joint_posDef _ (gibbsBlocks_posDef D Q)
  have hZ := partition_pos D Q
  let B : Joint := joint (polarBlocks D Q)
  let s := Real.sqrt ((partition D Q)⁻¹)
  have hgram : (joint (fun i => CFC.sqrt (gibbsBlocks D Q i))) *
      joint (recoveredBlocks D Q) * joint (fun i => CFC.sqrt (gibbsBlocks D Q i)) =
      B * Bᴴ := by
    simp only [B, joint, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    exact congrArg Matrix.blockDiagonal (funext (recovered_eq_polar_gram D Q hQ))
  have hscaled : s • (s • (B * Bᴴ)) = (s • B) * (s • B)ᴴ := by
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul]
  rw [rootFidelity, normalizedGibbs_eq_scaledJoint D Q hD hsum,
    partialTracePetz_eq_joint D Q hD hsum,
    sqrt_smul hG.posSemidef.nonneg (inv_nonneg.mpr hZ.le),
    sqrt_joint _ (gibbsBlocks_posDef D Q)]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hgram]
  change (CFC.sqrt (s • (s • (B * Bᴴ)))).trace.re = _
  rw [hscaled]
  have hnorm : (CFC.sqrt ((s • B) * (s • B)ᴴ)).trace.re = traceNorm (s • B) := by
    rw [← traceNorm_conjTranspose (s • B)]
    simp only [Foundation.FiniteTraceDistance.traceNorm, Matrix.conjTranspose_conjTranspose,
      RCLike.re_eq_complex_re]
  rw [hnorm, ← Complex.coe_smul,
    traceNorm_smul_nonneg _ _ (Real.sqrt_nonneg _), traceNorm_joint]
  rw [Real.sqrt_inv, div_eq_mul_inv, mul_comm]


/-- The strict sum-of-blocks deficit is exactly the strict root-fidelity failure. -/
private theorem rootFidelity_lt_sqrt_partition_iff (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) (hQ : Q.PosDef) :
    rootFidelity (normalizedGibbs (inputJoint Q) (referenceJoint D))
      (partialTracePetz (referenceJoint D) (partialTraceRight (inputJoint Q))) <
        Real.sqrt (partition D Q) ↔
      (∑ i, (traceNorm (polarBlocks D Q i) - (gibbsBlocks D Q i).trace.re)) < 0 := by
  have hZ := partition_pos D Q
  rw [rootFidelity_physical D Q hD hsum hQ, div_lt_iff₀ (Real.sqrt_pos.mpr hZ),
    ← pow_two (Real.sqrt (partition D Q)), Real.sq_sqrt hZ.le,
    Finset.sum_sub_distrib, sub_neg, partition]

open scoped CStarAlgebra
open NormedSpace (exp)
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
  (partitionFunction)
open D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritSecondFlag (mat_log)
open D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritFirstFlag
  (D₁ D₂ L₁ L₂ Q Q_posDef D1_strictlyPositive D2_strictlyPositive effects_sum mat_exp
    two_flag_overlap_lt_partition)

local notation "mat" => CStarMatrix.ofMatrix.symm
local notation "CQ" => CStarMatrix (Fin 3) (Fin 3) ℂ

local instance : NonUnitalContinuousFunctionalCalculus ℝ CQ IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance : NonnegSpectrumClass ℝ CQ := CStarAlgebra.instNonnegSpectrumClass'

private theorem mat_sqrt {X : CQ} (hX : 0 ≤ X) :
    mat (CFC.sqrt X) = CFC.sqrt (mat X) := by
  symm
  exact CFC.sqrt_unique (congrArg (fun Y : CQ => mat Y) (CFC.sqrt_mul_sqrt_self X hX))
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (CFC.sqrt_nonneg X))

/-- The input has two equal blocks `Q/2`. The reference has blocks `D₁/3`
and `D₂/3`. Both states and both retained marginals are faithful. -/
theorem exists_faithful_qutrit_two_flag_petz_fidelity_failure :
    ∃ ρ σ : Joint,
      let S := mpow σ (1 / 2)
      let W := mpow (partialTraceRight σ) (-(1 / 2))
      let P := S * ((W * partialTraceRight ρ * W) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * S
      ρ = inputJoint (mat Q.1) ∧
      σ = referenceJoint (fun i => mat (![D₁, D₂] i)) ∧
      ρ.PosDef ∧ ρ.trace = 1 ∧ σ.PosDef ∧ σ.trace = 1 ∧
      partialTraceRight ρ = mat Q.1 ∧ partialTraceRight σ = mixedQutrit ∧
      (partialTraceRight ρ).PosDef ∧ (partialTraceRight σ).PosDef ∧
      (normalizedGibbs ρ σ).PosDef ∧ (normalizedGibbs ρ σ).trace = 1 ∧
      P.PosDef ∧ P.trace = 1 ∧
      rootFidelity (normalizedGibbs ρ σ) P <
        Real.sqrt (gibbsOperator ρ σ).trace.re := by
  let effects : Fin 2 → CQ := ![D₁, D₂]
  let D : Fin 2 → Qutrit := fun i => mat (effects i)
  let q : Qutrit := mat Q.1
  let L : Fin 2 → CQ := fun i => CFC.log Q.1 + CFC.log (effects i)
  let : NormedAlgebra ℚ CQ := .restrictScalars ℚ ℂ _
  have hEffects (i : Fin 2) : IsStrictlyPositive (effects i) := by
    fin_cases i
    · simpa [effects] using D1_strictlyPositive
    · simpa [effects] using D2_strictlyPositive
  have hD (i : Fin 2) : (D i).PosDef := by
    have hA := hEffects i
    have hn : 0 ≤ mat (effects i) :=
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hA.nonneg
    have hu : IsUnit (mat (effects i)) :=
      hA.isUnit.map (CStarMatrix.ofMatrixRingEquiv (n := Fin 3) (A := ℂ)).symm.toMonoidHom
    exact Matrix.IsStrictlyPositive.posDef (hu.isStrictlyPositive hn)
  have hsum : ∑ i, D i = 1 := by
    rw [Fin.sum_univ_two]
    change mat (D₁ + D₂) = mat (1 : CQ)
    rw [effects_sum]
  have hQ : 0 ≤ Q.1 := Q.2.1
  have hblock (i : Fin 2) : gibbsBlocks D q i = mat (exp (L i)) := by
    rw [mat_exp]
    change exp (CFC.log (mat (effects i)) + CFC.log (mat Q.1)) =
      exp (mat (CFC.log Q.1) + mat (CFC.log (effects i)))
    rw [mat_log hQ.isSelfAdjoint, mat_log (hEffects i).isSelfAdjoint, add_comm]
  have hword (i : Fin 2) :
      polarBlocks D q i =
        mat (CFC.sqrt (exp (L i)) * CFC.sqrt (effects i) * CFC.sqrt Q.1) := by
    have hL : IsSelfAdjoint (L i) :=
      (IsSelfAdjoint.log (a := Q.1)).add (IsSelfAdjoint.log (a := effects i))
    rw [polarBlocks, hblock i]
    change CFC.sqrt (mat (exp (L i))) * CFC.sqrt (mat (effects i)) * CFC.sqrt (mat Q.1) =
      mat (CFC.sqrt (exp (L i))) * mat (CFC.sqrt (effects i)) * mat (CFC.sqrt Q.1)
    rw [mat_sqrt hL.exp_nonneg, mat_sqrt (hEffects i).nonneg, mat_sqrt hQ]
  have htrace (i : Fin 2) : (gibbsBlocks D q i).trace.re = partitionFunction (L i) := by
    rw [hblock i, partitionFunction]
  have hgap : (∑ i, traceNorm (polarBlocks D q i)) < partition D q := by
    rw [partition, Fin.sum_univ_two, Fin.sum_univ_two, hword 0, hword 1, htrace 0, htrace 1]
    simpa only [L, effects, Matrix.cons_val_zero, Matrix.cons_val_one, L₁, L₂] using
      two_flag_overlap_lt_partition
  obtain ⟨hρ, hρtrace⟩ := input_faithful_density q Q_posDef Q.2.2
  obtain ⟨hσ, hσtrace⟩ := reference_faithful_density D hD hsum
  obtain ⟨hG, hGtrace⟩ := normalizedGibbs_faithful_density D q hD hsum
  obtain ⟨hP, hPtrace⟩ := recovered_faithful_density D q hD hsum Q_posDef Q.2.2
  have hρm := input_marginal q
  have hσm := reference_marginal D hsum
  have hOne : (1 : Qutrit).PosDef := Matrix.PosDef.one
  have hMixed : mixedQutrit.PosDef := hOne.smul (by norm_num : (0 : ℝ) < 1 / 3)
  refine ⟨inputJoint q, referenceJoint D, ?_⟩
  dsimp only
  refine ⟨rfl, rfl, hρ, hρtrace, hσ, hσtrace, hρm, hσm,
    hρm.symm ▸ Q_posDef, hσm.symm ▸ hMixed, hG, hGtrace, hP, hPtrace, ?_⟩
  change rootFidelity (normalizedGibbs (inputJoint q) (referenceJoint D))
    (partialTracePetz (referenceJoint D) (partialTraceRight (inputJoint q))) <
      Real.sqrt (gibbsOperator (inputJoint q) (referenceJoint D)).trace.re
  rw [gibbsOperator_trace D q hD hsum]
  apply (rootFidelity_lt_sqrt_partition_iff D q hD hsum Q_posDef).2
  rw [Finset.sum_sub_distrib]
  exact sub_neg.mpr hgap

/-- The proposed lower bound for faithful states on a qutrit and a two-valued flag. -/
def claim : Prop :=
  ∀ ρ σ : Joint,
    ρ.PosDef → ρ.trace = 1 → σ.PosDef → σ.trace = 1 →
    (partialTraceRight ρ).PosDef → (partialTraceRight σ).PosDef →
    let S := mpow σ (1 / 2)
    let W := mpow (partialTraceRight σ) (-(1 / 2))
    let P := S * ((W * partialTraceRight ρ * W) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * S
    Real.sqrt (gibbsOperator ρ σ).trace.re ≤ rootFidelity (normalizedGibbs ρ σ) P

theorem result : ¬ claim := by
  intro h
  obtain ⟨ρ, σ, hw⟩ := exists_faithful_qutrit_two_flag_petz_fidelity_failure
  dsimp only at hw
  rcases hw with ⟨_, _, hρ, hρtrace, hσ, hσtrace, _, _, hρm, hσm, _, _, _, _, hlt⟩
  exact (not_lt_of_ge (h ρ σ hρ hρtrace hσ hσtrace hρm hσm)) hlt

end D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritPhysicalRefutation
