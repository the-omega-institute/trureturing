/- GID: D5/S3/Quantum/Recovery/QubitGibbsDeficit
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/QubitGibbsDeficit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact reducing qubit Gibbs deficit splits into conditional relative entropy loss and weighted block gaps. -/

import D5.S3.Quantum.Divergence.FannesRootFidelityHolevo
import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import D5.S3.Quantum.Divergence.LegacyRelativeEntropyBoundary
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.Recovery.BKMFlagRefinement
import D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
import D5.S3.Quantum.Recovery.CanonicalPetzEquality
import D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral

/-! The Gibbs deficit and its equality conditions on a finite qubit-environment system. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.QubitGibbsDeficit

open scoped BigOperators CStarAlgebra ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Divergence.LegacyRelativeEntropyBoundary
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMFlagRefinement (joint joint_posDef cfc_joint)

variable {E : Type*} [Fintype E] [DecidableEq E]

local notation "mat" => CStarMatrix.ofMatrix.symm

/-- A block diagonal operator in the retained-qubit basis, with the qubit index first. -/
def retainedBlock (T : Fin 2 → Matrix E E ℂ) : Matrix (Fin 2 × E) (Fin 2 × E) ℂ :=
  Matrix.reindex (Equiv.prodComm E (Fin 2)) (Equiv.prodComm E (Fin 2)) (joint T)

private theorem block_apply (T : Fin 2 → Matrix E E ℂ) (i j : Fin 2) (e f : E) :
    retainedBlock T (i, e) (j, f) = if i = j then T i e f else 0 := by
  simp [retainedBlock, joint, Matrix.blockDiagonal_apply]

private theorem cfc_block (f : ℝ → ℝ) (T : Fin 2 → Matrix E E ℂ)
    (hT : ∀ i, (T i).IsHermitian) :
    cfc f (retainedBlock T) = retainedBlock (fun i => cfc f (T i)) := by
  rw [retainedBlock, Matrix.cfc_reindex, cfc_joint f T hT]
  rfl

private theorem block_posDef (T : Fin 2 → Matrix E E ℂ) (hT : ∀ i, (T i).PosDef) :
    (retainedBlock T).PosDef :=
  (joint_posDef T hT).submatrix (Equiv.prodComm (Fin 2) E).injective

private theorem mat_psd {n : Type*} [Fintype n] [DecidableEq n] (ρ : DensityState n) :
    (mat ρ.1).PosSemidef :=
  density_posSemidef (toLegacyDensityState ρ)

/-- The actual retained marginal obtained by tracing out the environment. -/
def retainedMarginal (ρ : DensityState (Fin 2 × E)) : DensityState (Fin 2) :=
  fromLegacyDensityState (marginalRight (toLegacyDensityState ρ))

private theorem trace_block (T : Fin 2 → Matrix E E ℂ) :
    (retainedBlock T).trace = ∑ i, (T i).trace := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp [block_apply, Matrix.trace]

private def blockState (γ : Fin 2 → DensityState E) (w : Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : DensityState (Fin 2 × E) :=
  ⟨CStarMatrix.ofMatrix (retainedBlock (fun i => w i • mat (γ i).1)), by
    apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.PosSemidef.nonneg
    exact (D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.MatrixBlocks.blockDiagonal_psd
      _ (fun i => (mat_psd (γ i)).smul (hw i))).submatrix (Equiv.prodComm (Fin 2) E), by
    change (retainedBlock (fun i => w i • mat (γ i).1)).trace = 1
    rw [trace_block]
    simp only [Matrix.trace_smul]
    change ∑ i, w i • Matrix.trace (γ i).1 = 1
    simp only [DensityState.trace_eq_one, Complex.real_smul, mul_one]
    exact_mod_cast hs⟩

private theorem marginal_blockState (γ : Fin 2 → DensityState E) (w : Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    mat (retainedMarginal (blockState γ w hw hs)).1 = Matrix.diagonal (fun i => (w i : ℂ)) := by
  ext i j
  change (∑ e : E, retainedBlock (fun i => w i • mat (γ i).1) (i, e) (j, e)) = _
  by_cases hij : i = j
  · subst j
    simp only [block_apply, ite_true, Matrix.diagonal_apply_eq]
    change Matrix.trace (w i • mat (γ i).1) = _
    rw [Matrix.trace_smul]
    change w i • Matrix.trace (γ i).1 = _
    simp [Complex.real_smul]
  · simp [block_apply, Matrix.diagonal_apply_ne _ hij, hij]

/-- Faithful comparison reference when both block densities are faithful. -/
def qubitBlockReference (γ : Fin 2 → DensityState E) : DensityState (Fin 2 × E) :=
  blockState γ (fun _ => 1 / 2) (fun _ => by norm_num) (by norm_num [Fin.sum_univ_two])

private theorem reference_posDef (γ : Fin 2 → DensityState E)
    (hγ : ∀ i, (mat (γ i).1).PosDef) : (mat (qubitBlockReference γ).1).PosDef :=
  block_posDef _ (fun i => (hγ i).smul (by norm_num))

private theorem marginal_reference (γ : Fin 2 → DensityState E) :
    mat (retainedMarginal (qubitBlockReference γ)).1 = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold qubitBlockReference
  rw [marginal_blockState]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij, Complex.real_smul]

private theorem mat_log {n : Type*} [Fintype n] [DecidableEq n] (ρ : DensityState n) :
    mat (CFC.log ρ.1) = CFC.log (mat ρ.1) := by
  let M : Matrix n n ℂ := mat ρ.1
  have hM : M.IsHermitian := (mat_psd ρ).isHermitian
  have hlog : CStarMatrix.ofMatrix (cfc Real.log M) = CFC.log ρ.1 :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log M
      (M.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hM (by exact hM)
  exact congrArg CStarMatrix.ofMatrix.symm hlog.symm

open private log_smul_faithful from D5.S3.Quantum.Recovery.BKMFlagRefinement

private theorem trace_mul_scalar_blocks (R : Matrix (Fin 2 × E) (Fin 2 × E) ℂ)
    (a : Fin 2 → ℝ) :
    (R * retainedBlock (fun i => a i • (1 : Matrix E E ℂ))).trace.re =
      ∑ i, ((partialTraceRight R) i i).re * a i := by
  have hdiag : retainedBlock (fun i => a i • (1 : Matrix E E ℂ)) =
      Matrix.diagonal (fun x : Fin 2 × E => (a x.1 : ℂ)) := by
    ext ⟨i, e⟩ ⟨j, f⟩
    by_cases hij : i = j <;> by_cases hef : e = f <;>
      simp [block_apply, hij, hef, Matrix.diagonal_apply, Matrix.one_apply, Complex.real_smul]
  rw [hdiag, Matrix.trace, Fintype.sum_prod_type, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply, Matrix.mul_diagonal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, partialTraceRight, Complex.re_sum, Finset.sum_mul]

private theorem block_sub (T U : Fin 2 → Matrix E E ℂ) :
    retainedBlock (fun i => T i - U i) = retainedBlock T - retainedBlock U := by
  ext ⟨i, e⟩ ⟨j, f⟩
  by_cases hij : i = j <;> simp [block_apply, hij]

private theorem entropy_cross {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : DensityState n) :
    finiteTraceLogRelativeEntropy ρ σ = -vonNeumannEntropy (toLegacyDensityState ρ) -
      (mat ρ.1 * CFC.log (mat σ.1)).trace.re := by
  rw [← legacy_quantumRelativeEntropy_eq_finite_branch,
    quantum_relative_entropy_eq_neg_entropy_sub_cross]
  change _ - (mat ρ.1 * mat (CFC.log σ.1)).trace.re = _
  rw [mat_log]

variable [Nonempty E]

/-- Normalized Gibbs state in each retained block. -/
def blockGibbs (B : Fin 2 → CStarMatrix E E ℂ) (hB : ∀ i, IsSelfAdjoint (B i))
    (i : Fin 2) : DensityState E :=
  fromLegacyDensityState (gibbsState (B i) (hB i))

/-- Conditional entropy plus the energy at the reducing field. -/
def gibbsValue (B : Fin 2 → CStarMatrix E E ℂ) (ρ : DensityState (Fin 2 × E)) : ℝ :=
  vonNeumannEntropy (toLegacyDensityState ρ) -
    vonNeumannEntropy (toLegacyDensityState (retainedMarginal ρ)) +
    (mat ρ.1 * retainedBlock (fun i => mat (B i))).trace.re

/-- The difference of the joint and retained finite trace-log relative entropies.
This is the Umegaki relative entropy loss when `supp ρ ⊆ supp τ` and the support of
`retainedMarginal ρ` is contained in the support of `retainedMarginal τ`. -/
def conditionalLoss (ρ τ : DensityState (Fin 2 × E)) : ℝ :=
  finiteTraceLogRelativeEntropy ρ τ -
    finiteTraceLogRelativeEntropy (retainedMarginal ρ) (retainedMarginal τ)

private theorem blockGibbs_posDef (B : Fin 2 → CStarMatrix E E ℂ)
    (hB : ∀ i, IsSelfAdjoint (B i)) (i : Fin 2) :
    (mat (blockGibbs B hB i).1).PosDef :=
  gibbs_state_posDef (B i) (hB i)

private theorem log_reference (B : Fin 2 → CStarMatrix E E ℂ) (hB : ∀ i, IsSelfAdjoint (B i)) :
    CFC.log (mat (qubitBlockReference (blockGibbs B hB)).1) =
      retainedBlock (fun i => mat (B i) -
        (Real.log (partitionFunction (B i)) - Real.log (1 / 2)) • (1 : Matrix E E ℂ)) := by
  change cfc Real.log (retainedBlock (fun i => (1 / 2 : ℝ) • mat (blockGibbs B hB i).1)) = _
  rw [cfc_block _ _ (fun i => ((blockGibbs_posDef B hB i).smul
    (show (0 : ℝ) < 1 / 2 by norm_num)).isHermitian)]
  congr 1
  funext i
  change CFC.log ((1 / 2 : ℝ) • mat (blockGibbs B hB i).1) = _
  rw [log_smul_faithful (blockGibbs_posDef B hB i) (by norm_num), ← mat_log]
  change _ + mat (CFC.log (gibbsState (B i) (hB i)).1) = _
  rw [log_gibbs_state]
  change Real.log (1 / 2) • (1 : Matrix E E ℂ) +
    (mat (B i) - Real.log (partitionFunction (B i)) • 1) = _
  rw [sub_smul]
  abel

private theorem populations_sum (ρ : DensityState (Fin 2 × E)) :
    ∑ i, (mat (retainedMarginal ρ).1 i i).re = 1 := by
  rw [← Complex.re_sum]
  exact congrArg Complex.re (DensityState.trace_eq_one (retainedMarginal ρ))

/-- At every physical trial state the reducing Gibbs deficit is exactly the conditional
relative entropy loss at the equal-mass block Gibbs reference plus the weighted block gaps. -/
theorem reducing_qubit_gibbs_deficit (B : Fin 2 → CStarMatrix E E ℂ)
    (hB : ∀ i, IsSelfAdjoint (B i)) (ρ : DensityState (Fin 2 × E)) :
    let g := fun i => Real.log (partitionFunction (B i))
    let m := max (g 0) (g 1)
    m - gibbsValue B ρ = conditionalLoss ρ (qubitBlockReference (blockGibbs B hB)) +
      ∑ i, (mat (retainedMarginal ρ).1 i i).re * (m - g i) := by
  dsimp only
  let p := fun i => (mat (retainedMarginal ρ).1 i i).re
  let g := fun i => Real.log (partitionFunction (B i))
  let m := max (g 0) (g 1)
  let l := Real.log (1 / 2)
  change m - gibbsValue B ρ = conditionalLoss ρ (qubitBlockReference (blockGibbs B hB)) +
    ∑ i, p i * (m - g i)
  have hp : ∑ i, p i = 1 := populations_sum ρ
  have hJoint := trace_mul_scalar_blocks (mat ρ.1) (fun i => g i - l)
  change _ = ∑ i, p i * (g i - l) at hJoint
  have hMarg : CFC.log (mat (retainedMarginal (qubitBlockReference (blockGibbs B hB))).1) =
      l • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [marginal_reference, log_smul_faithful Matrix.PosDef.one (by norm_num),
      CFC.log_one, add_zero]
  unfold gibbsValue conditionalLoss
  rw [entropy_cross, entropy_cross, log_reference B hB, block_sub, mul_sub,
    Matrix.trace_sub, Complex.sub_re, hJoint, hMarg, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul]
  change _ = _ - (_ - (l • Matrix.trace (retainedMarginal ρ).1).re) + _
  rw [DensityState.trace_eq_one]
  simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hp, one_mul]
  ring

#print axioms reducing_qubit_gibbs_deficit

open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Recovery.CanonicalPetzEquality
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery

private theorem exists_partialTraceChannel :
    ∃ Φ : QuantumChannel (Fin 2 × E) (Fin 2), ∀ X : Matrix (Fin 2 × E) (Fin 2 × E) ℂ,
      mat (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = partialTraceRight X := by
  obtain ⟨Φ, hΦ⟩ :=
    D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.exists_eraseChannel (n := Fin 2) (ι := E)
  refine ⟨Φ, fun X => ?_⟩
  rw [hΦ]
  ext i j
  simp only [partialTraceRight, Matrix.sum_apply, Matrix.submatrix_apply]

private theorem mapState_partialTrace
    {Φ : QuantumChannel (Fin 2 × E) (Fin 2)}
    (hΦ : ∀ X : Matrix (Fin 2 × E) (Fin 2 × E) ℂ,
      mat (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = partialTraceRight X)
    (ρ : DensityState (Fin 2 × E)) : Φ.mapState ρ = retainedMarginal ρ := by
  apply Subtype.ext
  exact congrArg CStarMatrix.ofMatrix (hΦ (mat ρ.1))

private theorem reference_support (γ : Fin 2 → DensityState E)
    (hγ : ∀ i, (mat (γ i).1).PosDef) (ρ : DensityState (Fin 2 × E)) :
    SupportContained ρ (qubitBlockReference γ) ∧
      SupportContained (retainedMarginal ρ) (retainedMarginal (qubitBlockReference γ)) := by
  refine ⟨support_of_posDef _ _ (reference_posDef γ hγ), support_of_posDef _ _ ?_⟩
  rw [marginal_reference]
  exact Matrix.PosDef.one.smul (by norm_num)

private theorem conditionalLoss_nonneg (γ : Fin 2 → DensityState E)
    (hγ : ∀ i, (mat (γ i).1).PosDef) (ρ : DensityState (Fin 2 × E)) :
    0 ≤ conditionalLoss ρ (qubitBlockReference γ) := by
  obtain ⟨Φ, hΦ⟩ := exists_partialTraceChannel (E := E)
  have h := extended_quantum_relative_entropy_channel_dpi Φ ρ (qubitBlockReference γ)
  rw [mapState_partialTrace hΦ, mapState_partialTrace hΦ] at h
  obtain ⟨hJoint, hMarginal⟩ := reference_support γ hγ ρ
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support hJoint,
    extendedQuantumRelativeEntropy_eq_coe_of_support hMarginal] at h
  exact sub_nonneg.mpr (WithTop.coe_le_coe.mp h)

private theorem trace_tensor_identity (X : Matrix (Fin 2 × E) (Fin 2 × E) ℂ)
    (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (X * (Y ⊗ₖ (1 : Matrix E E ℂ))).trace = (partialTraceRight X * Y).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, partialTraceRight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

private theorem partialTrace_adjoint
    {Φ : QuantumChannel (Fin 2 × E) (Fin 2)}
    (hΦ : ∀ X : Matrix (Fin 2 × E) (Fin 2 × E) ℂ,
      mat (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = partialTraceRight X)
    (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    krausAdjoint (actual_kraus_representation Φ).kraus Y = Y ⊗ₖ (1 : Matrix E E ℂ) := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  rw [actual_kraus_trace_pair, hΦ, trace_tensor_identity]

private abbrev root (A : Matrix E E ℂ) : Matrix E E ℂ := cfc Real.sqrt A

private theorem root_eq_sqrt (A : Matrix E E ℂ) (hA : A.PosSemidef) :
    root A = CFC.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt _ hA.nonneg,
    cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := Real.sqrt_zero)]

private theorem root_nonneg (A : Matrix E E ℂ) (hA : A.PosSemidef) : 0 ≤ root A := by
  rw [root_eq_sqrt _ hA]
  exact CFC.sqrt_nonneg A

private theorem root_square (A : Matrix E E ℂ) (hA : A.PosSemidef) : root A * root A = A := by
  rw [root_eq_sqrt _ hA]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

private theorem root_half (A : Matrix E E ℂ) (hA : A.PosSemidef) :
    root ((1 / 2 : ℝ) • A) = (√(1 / 2 : ℝ)) • root A := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hcoeff : (√(1 / 2 : ℝ)) * √(1 / 2 : ℝ) = 1 / 2 := Real.mul_self_sqrt hhalf
  rw [root_eq_sqrt _ (hA.smul hhalf)]
  apply CFC.sqrt_unique _ (smul_nonneg (Real.sqrt_nonneg _) (root_nonneg A hA))
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hcoeff, root_square A hA]

private theorem root_reference (γ : Fin 2 → DensityState E) :
    cfc Real.sqrt (mat (qubitBlockReference γ).1) =
      retainedBlock (fun i => (√(1 / 2 : ℝ)) • root (mat (γ i).1)) := by
  change cfc Real.sqrt (retainedBlock (fun i => (1 / 2 : ℝ) • mat (γ i).1)) = _
  rw [cfc_block _ _ (fun i => ((mat_psd (γ i)).smul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)).isHermitian)]
  congr 1
  funext i
  exact root_half _ (mat_psd (γ i))

private theorem cfc_scalar_qubit (f : ℝ → ℝ) (a : ℝ) :
    cfc f (a • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      f a • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [← Algebra.algebraMap_eq_smul_one, cfc_algebraMap]

private theorem sandwiched_block_apply (T : Fin 2 → Matrix E E ℂ)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (e f : E) :
    (retainedBlock T * (P ⊗ₖ (1 : Matrix E E ℂ)) * retainedBlock T) (i,e) (j,f) =
      P i j * (T i * T j) e f := by
  have hleft (k : Fin 2) (g : E) :
      (retainedBlock T * (P ⊗ₖ (1 : Matrix E E ℂ))) (i,e) (k,g) =
        T i e g * P i k := by
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, block_apply, Matrix.kronecker_apply,
      Matrix.one_apply, ite_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change (∑ k : Fin 2, ∑ g : E,
    (retainedBlock T * (P ⊗ₖ (1 : Matrix E E ℂ))) (i,e) (k,g) *
      retainedBlock T (k,g) (j,f)) = _
  simp only [hleft, block_apply, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

private theorem conditionalLoss_eq_zero_iff_entries (γ : Fin 2 → DensityState E)
    (hγ : ∀ i, (mat (γ i).1).PosDef) (ρ : DensityState (Fin 2 × E)) :
    conditionalLoss ρ (qubitBlockReference γ) = 0 ↔
      ∀ (i j : Fin 2) (e f : E), mat ρ.1 (i,e) (j,f) =
        mat (retainedMarginal ρ).1 i j * (root (mat (γ i).1) * root (mat (γ j).1)) e f := by
  obtain ⟨Φ, hΦ⟩ := exists_partialTraceChannel (E := E)
  let τ := qubitBlockReference γ
  let P := mat (retainedMarginal ρ).1
  let T := fun i => root (mat (γ i).1)
  obtain ⟨R, hR, _, hEq⟩ := supported_entropy_equality_iff_fixed_petz_recovery Φ τ
  have hQ : mat (Φ.mapState τ).1 = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [mapState_partialTrace hΦ, marginal_reference]
  have hW : spectralInverseSqrt (mat (Φ.mapState τ).1) =
      (√(1 / 2 : ℝ))⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hQ, spectralInverseSqrt, cfc_scalar_qubit]
  have hS : spectralSupport (mat (Φ.mapState τ).1) = 1 := by
    rw [hQ, spectralSupport, cfc_scalar_qubit]
    norm_num
  have hRec : ∀ (i j : Fin 2) (e f : E),
      mat (R.mapState (Φ.mapState ρ)).1 (i,e) (j,f) = P i j * (T i * T j) e f := by
    intro i j e f
    have h := hR P
    -- The channel input is precisely the actual reduced density matrix.
    have hInput : (Φ.mapState ρ).1 = CStarMatrix.ofMatrix P :=
      congrArg Subtype.val (mapState_partialTrace hΦ ρ)
    change mat (R.toCompletelyPositiveMap (Φ.mapState ρ).1) (i,e) (j,f) = _
    rw [hInput, h, hS, sub_self, Matrix.zero_mul, Matrix.trace_zero, zero_smul, add_zero]
    let W := spectralInverseSqrt (mat (Φ.mapState τ).1)
    let S := cfc Real.sqrt (mat τ.1)
    have hsum :
        (∑ c, S * Matrix.conjTranspose ((actual_kraus_representation Φ).kraus c) * W * P * W *
            (actual_kraus_representation Φ).kraus c * S) =
          S * krausAdjoint (actual_kraus_representation Φ).kraus (W * P * W) * S := by
      simp only [krausAdjoint, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    rw [hsum, partialTrace_adjoint hΦ]
    change (S * ((W * P * W) ⊗ₖ (1 : Matrix E E ℂ)) * S) (i,e) (j,f) = _
    let r := √(1 / 2 : ℝ)
    have hscale : r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hr : ((r⁻¹ : ℝ) : ℂ) * (r : ℂ) = 1 := by
      exact_mod_cast inv_mul_cancel₀ hscale
    change (cfc Real.sqrt (mat (qubitBlockReference γ).1) *
      ((spectralInverseSqrt (mat (Φ.mapState τ).1) * P *
        spectralInverseSqrt (mat (Φ.mapState τ).1)) ⊗ₖ (1 : Matrix E E ℂ)) *
      cfc Real.sqrt (mat (qubitBlockReference γ).1)) (i,e) (j,f) = _
    rw [hW, root_reference, sandwiched_block_apply]
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one,
      smul_smul, Matrix.smul_apply, Complex.real_smul]
    have hcancel (x y : ℂ) :
        (((r⁻¹ : ℝ) : ℂ) * (((r⁻¹ : ℝ) : ℂ) * x)) *
          ((r : ℂ) * ((r : ℂ) * y)) = x * y := by
      calc
        _ = (((r⁻¹ : ℝ) : ℂ) * (r : ℂ)) ^ 2 * (x * y) := by ring
        _ = _ := by rw [hr, one_pow, one_mul]
    simpa only [Complex.ofReal_inv] using hcancel (P i j) ((T i * T j) e f)

  have h := hEq ρ (reference_support γ hγ ρ).1
  rw [mapState_partialTrace hΦ ρ, mapState_partialTrace hΦ τ] at h
  rw [conditionalLoss, sub_eq_zero]
  constructor
  · intro hz
    have he := h.mp hz
    rw [← mapState_partialTrace hΦ ρ] at he
    intro i j e f
    exact (congrArg (fun σ : DensityState (Fin 2 × E) => mat σ.1 (i,e) (j,f)) he).symm.trans
      (hRec i j e f)
  · intro he
    apply h.mpr
    rw [← mapState_partialTrace hΦ ρ]
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    ext ⟨i,e⟩ ⟨j,f⟩
    exact (hRec i j e f).trans (he i j e f).symm

private theorem root_trace_rigidity (γ δ : DensityState E)
    (h : (root (mat γ.1) * root (mat δ.1)).trace = 1) : γ = δ := by
  let A := root (mat γ.1)
  let B := root (mat δ.1)
  have hA : Matrix.conjTranspose A = A := (Matrix.nonneg_iff_posSemidef.mp (root_nonneg _ (mat_psd γ))).isHermitian
  have hB : Matrix.conjTranspose B = B := (Matrix.nonneg_iff_posSemidef.mp (root_nonneg _ (mat_psd δ))).isHermitian
  have hAA : A * A = mat γ.1 := root_square _ (mat_psd γ)
  have hBB : B * B = mat δ.1 := root_square _ (mat_psd δ)
  change (A * B).trace = 1 at h
  have hBA : (B * A).trace = 1 := (Matrix.trace_mul_comm B A).trans h
  have hz : (Matrix.conjTranspose (A - B) * (A - B)).trace = 0 := by
    rw [Matrix.conjTranspose_sub, hA, hB, sub_mul, mul_sub, mul_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, hAA, hBB, h, hBA]
    change Matrix.trace γ.1 - 1 - (1 - Matrix.trace δ.1) = 0
    simp
  have hab := sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz)
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  rw [← hAA, ← hBB, hab]

private theorem real_diagonal (ρ : DensityState (Fin 2)) (i : Fin 2) :
    ((mat ρ.1 i i).re : ℂ) = mat ρ.1 i i := by
  apply Complex.ext
  · simp
  · exact (Complex.nonneg_iff.mp ((mat_psd ρ).diag_nonneg (i := i))).2

private theorem conditionalLoss_eq_zero_iff (γ : Fin 2 → DensityState E)
    (hγ : ∀ i, (mat (γ i).1).PosDef) (ρ : DensityState (Fin 2 × E)) :
    let P := mat (retainedMarginal ρ).1
    conditionalLoss ρ (qubitBlockReference γ) = 0 ↔
      mat ρ.1 = retainedBlock (fun i => (P i i).re • mat (γ i).1) ∨
        (γ 0 = γ 1 ∧ mat ρ.1 = P ⊗ₖ mat (γ 0).1) := by
  dsimp only
  let P := mat (retainedMarginal ρ).1
  change _ ↔ mat ρ.1 = retainedBlock (fun i => (P i i).re • mat (γ i).1) ∨
    (γ 0 = γ 1 ∧ mat ρ.1 = P ⊗ₖ mat (γ 0).1)
  rw [conditionalLoss_eq_zero_iff_entries γ hγ]
  have hSQ (i : Fin 2) : root (mat (γ i).1) * root (mat (γ i).1) = mat (γ i).1 :=
    root_square _ (mat_psd (γ i))
  have hdiag (i : Fin 2) : ((P i i).re : ℂ) = P i i :=
    real_diagonal (retainedMarginal ρ) i
  have hγsame (h : γ 0 = γ 1) (i : Fin 2) : γ i = γ 0 := by
    fin_cases i
    · rfl
    · exact h.symm
  constructor
  · intro h
    by_cases h01 : P 0 1 = 0
    · left
      have h10 : P 1 0 = 0 := by
        have hHerm := (mat_psd (retainedMarginal ρ)).isHermitian
        change P.IsHermitian at hHerm
        simpa [h01, Matrix.conjTranspose_apply] using congrFun (congrFun hHerm 1) 0 |>.symm
      ext ⟨i,e⟩ ⟨j,f⟩
      rw [h, block_apply]
      by_cases hij : i = j
      · subst j
        rw [ite_eq_left rfl, hSQ]
        simp only [Matrix.smul_apply, Complex.real_smul, hdiag]
        rfl
      · rw [ite_eq_right hij]
        have hpij : P i j = 0 := by
          fin_cases i <;> fin_cases j
          · exact (hij rfl).elim
          · exact h01
          · exact h10
          · exact (hij rfl).elim
        change P i j * _ = 0
        rw [hpij, zero_mul]
    · right
      have hsum : P 0 1 = P 0 1 * (root (mat (γ 0).1) * root (mat (γ 1).1)).trace := by
        change (∑ e : E, mat ρ.1 (0,e) (1,e)) = _
        simp only [h, Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
        rfl
      have hγ01 := root_trace_rigidity (γ 0) (γ 1)
        (mul_left_cancel₀ h01 (by simpa only [mul_one] using hsum.symm))
      refine ⟨hγ01, ?_⟩
      ext ⟨i,e⟩ ⟨j,f⟩
      rw [h, hγsame hγ01 i, hγsame hγ01 j, hSQ, Matrix.kronecker_apply]
  · rintro (h | ⟨h01, h⟩) i j e f
    · rw [h, block_apply]
      by_cases hij : i = j
      · subst j
        rw [ite_eq_left rfl, hSQ]
        simp only [Matrix.smul_apply, Complex.real_smul, hdiag]
        rfl
      · have hpij : P i j = 0 := by
          change (∑ e : E, mat ρ.1 (i,e) (j,e)) = _
          rw [h]
          simp [block_apply, hij]
        rw [ite_eq_right hij]
        change 0 = P i j * _
        rw [hpij, zero_mul]
    · rw [h, hγsame h01 i, hγsame h01 j, hSQ, Matrix.kronecker_apply]

private def endpointWeight (i j : Fin 2) : ℝ := if i = j then 1 else 0

/-- The block Gibbs density with a pure retained basis state at the given label. -/
def gibbsEndpoint (B : Fin 2 → CStarMatrix E E ℂ) (hB : ∀ i, IsSelfAdjoint (B i))
    (i : Fin 2) : DensityState (Fin 2 × E) :=
  blockState (blockGibbs B hB) (endpointWeight i) (fun j => by
    by_cases hij : i = j <;> simp [endpointWeight, hij]) (by
      simp [endpointWeight, Finset.sum_ite_eq, Finset.sum_ite_eq'])

/-- The largest block Gibbs value is attained at every winning pure retained basis state.
An arbitrary density maximizes exactly when it puts weight only on winning blocks and
is their block Gibbs mixture, or is a product with the common Gibbs density. -/
theorem reducing_qubit_gibbs_argmax (B : Fin 2 → CStarMatrix E E ℂ)
    (hB : ∀ i, IsSelfAdjoint (B i)) :
    let γ := blockGibbs B hB
    let g := fun i => Real.log (partitionFunction (B i))
    let m := max (g 0) (g 1)
    IsGreatest (Set.range (gibbsValue B)) m ∧
      (∀ i, g i = m →
        gibbsValue B (gibbsEndpoint B hB i) = m ∧
          mat (retainedMarginal (gibbsEndpoint B hB i)).1 = Matrix.single i i 1) ∧
      ∀ ρ, let P := mat (retainedMarginal ρ).1
        gibbsValue B ρ = m ↔
          (∀ i, (P i i).re = 0 ∨ g i = m) ∧
          (mat ρ.1 = retainedBlock (fun i => (P i i).re • mat (γ i).1) ∨
            (γ 0 = γ 1 ∧ mat ρ.1 = P ⊗ₖ mat (γ 0).1)) := by
  dsimp only
  let γ := blockGibbs B hB
  let g := fun i => Real.log (partitionFunction (B i))
  let m := max (g 0) (g 1)
  have hg (i : Fin 2) : g i ≤ m := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hγ := blockGibbs_posDef B hB
  have htrial (ρ : DensityState (Fin 2 × E)) :
      gibbsValue B ρ ≤ m ∧
        (gibbsValue B ρ = m ↔
          (∀ i, (mat (retainedMarginal ρ).1 i i).re = 0 ∨ g i = m) ∧
            (mat ρ.1 = retainedBlock (fun i => (mat (retainedMarginal ρ).1 i i).re • mat (γ i).1) ∨
              (γ 0 = γ 1 ∧ mat ρ.1 = mat (retainedMarginal ρ).1 ⊗ₖ mat (γ 0).1))) := by
    let p := fun i => (mat (retainedMarginal ρ).1 i i).re
    have hd : m - gibbsValue B ρ = conditionalLoss ρ (qubitBlockReference γ) +
        ∑ i, p i * (m - g i) := reducing_qubit_gibbs_deficit B hB ρ
    have hp (i : Fin 2) : 0 ≤ p i :=
      (Complex.nonneg_iff.mp ((mat_psd (retainedMarginal ρ)).diag_nonneg (i := i))).1
    have hn (i : Fin 2) (_ : i ∈ Finset.univ) : 0 ≤ p i * (m - g i) :=
      mul_nonneg (hp i) (sub_nonneg.mpr (hg i))
    have hsum := Finset.sum_nonneg hn
    have hLoss := conditionalLoss_nonneg γ hγ ρ
    have hsumzero : (∑ i, p i * (m - g i)) = 0 ↔ ∀ i, p i = 0 ∨ g i = m := by
      rw [Finset.sum_eq_zero_iff_of_nonneg hn]
      simp only [Finset.mem_univ, true_implies, mul_eq_zero, sub_eq_zero, eq_comm (a := m)]
    refine ⟨by linarith, ?_⟩
    have hzero := conditionalLoss_eq_zero_iff γ hγ ρ
    dsimp only at hzero
    change _ ↔ (∀ i, p i = 0 ∨ g i = m) ∧ _
    rw [← hsumzero, ← hzero]
    constructor
    · intro h
      constructor <;> linarith
    · rintro ⟨hs, hl⟩
      linarith
  have he (i : Fin 2) (hi : g i = m) :
      gibbsValue B (gibbsEndpoint B hB i) = m ∧
        mat (retainedMarginal (gibbsEndpoint B hB i)).1 = Matrix.single i i 1 := by
    let ρ := gibbsEndpoint B hB i
    have hp : mat (retainedMarginal ρ).1 = Matrix.diagonal (fun j => (endpointWeight i j : ℂ)) :=
      marginal_blockState _ _ _ _
    refine ⟨(htrial ρ).2.mpr ⟨?_, Or.inl ?_⟩, ?_⟩
    · intro j
      by_cases hij : i = j
      · exact Or.inr (hij ▸ hi)
      · left
        change (mat (retainedMarginal ρ).1 j j).re = 0
        rw [hp, Matrix.diagonal_apply_eq]
        simp [endpointWeight, hij]
    · change retainedBlock (fun j => endpointWeight i j • mat (γ j).1) =
        retainedBlock (fun j => (mat (retainedMarginal ρ).1 j j).re • mat (γ j).1)
      rw [hp]
      simp only [Matrix.diagonal_apply_eq, Complex.ofReal_re]
    · rw [hp]
      ext j k
      by_cases hij : i = j <;> by_cases hik : i = k <;>
        simp_all [Matrix.diagonal_apply, Matrix.single, endpointWeight, eq_comm]
  refine ⟨⟨?_, ?_⟩, he, fun ρ => (htrial ρ).2⟩
  · rcases le_total (g 0) (g 1) with h | h
    · exact ⟨gibbsEndpoint B hB 1, (he 1 (max_eq_right h).symm).1⟩
    · exact ⟨gibbsEndpoint B hB 0, (he 0 (max_eq_left h).symm).1⟩
  · rintro _ ⟨ρ, rfl⟩
    exact (htrial ρ).1

#print axioms reducing_qubit_gibbs_argmax

private theorem basis_marginal_pure (i : Fin 2) :
    ∃ v : EuclideanSpace ℂ (Fin 2), ‖v‖ = 1 ∧
      Matrix.single i i (1 : ℂ) = Matrix.vecMulVec v.ofLp (star v.ofLp) := by
  refine ⟨EuclideanSpace.single i 1, by simp, ?_⟩
  ext j k
  by_cases hij : j = i <;> by_cases hik : k = i <;>
    simp [Matrix.single, Matrix.vecMulVec_apply, EuclideanSpace.single, hij, hik] <;> aesop

omit [Nonempty E] in
private theorem endpoint_sum (γ : Fin 2 → DensityState E) (p : Fin 2 → ℝ) :
    retainedBlock (fun i => p i • mat (γ i).1) =
      ∑ i, p i • retainedBlock (fun j => endpointWeight i j • mat (γ j).1) := by
  ext ⟨j, e⟩ ⟨k, f⟩
  by_cases hjk : j = k
  · subst k
    fin_cases j <;> simp [block_apply, endpointWeight, Matrix.sum_apply, Matrix.smul_apply]
  · simp [Matrix.sum_apply, Matrix.smul_apply, block_apply, hjk]

omit [DecidableEq E] [Nonempty E] in
private theorem trace_score_sum {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (X : ι → Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (Z : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) :
    ((∑ i, p i • X i) * Z).trace.re = ∑ i, p i * (X i * Z).trace.re := by
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, Complex.smul_re, smul_eq_mul]

private theorem score_le_weighted_max (p a : Fin 2 → ℝ) (m : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (ha : ∀ i, p i = 0 ∨ a i ≤ m) :
    ∑ i, p i * a i ≤ m := by
  calc
    _ ≤ ∑ i, p i * m := Finset.sum_le_sum fun i _ => by
      rcases ha i with h | h
      · simp [h]
      · exact mul_le_mul_of_nonneg_left h (hp i)
    _ = _ := by rw [← Finset.sum_mul, hp1, one_mul]

private theorem product_score_max (γ : DensityState E) (Z : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) :
    ∃ P : DensityState (Fin 2),
      (∃ v : EuclideanSpace ℂ (Fin 2), ‖v‖ = 1 ∧
        mat P.1 = Matrix.vecMulVec v.ofLp (star v.ofLp)) ∧
      ∀ R : DensityState (Fin 2),
        (((mat R.1) ⊗ₖ mat γ.1) * Z).trace.re ≤ (((mat P.1) ⊗ₖ mat γ.1) * Z).trace.re := by
  let ray (v : EuclideanSpace ℂ (Fin 2)) := Matrix.vecMulVec v.ofLp (star v.ofLp)
  let f (v : EuclideanSpace ℂ (Fin 2)) := ((ray v ⊗ₖ mat γ.1) * Z).trace.re
  have hcont : Continuous f := by
    unfold f ray
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
      Matrix.vecMulVec_apply, Pi.star_apply]
    fun_prop
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ (Fin 2)) 1).exists_isMaxOn
    ⟨EuclideanSpace.single 0 1, by simp⟩ hcont.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa using hv
  let P : DensityState (Fin 2) := ⟨CStarMatrix.ofMatrix (ray v),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (Matrix.posSemidef_vecMulVec_self_star v.ofLp).nonneg, by
      change (ray v).trace = 1
      unfold ray
      rw [D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth.pure_trace, hvnorm]
      norm_num⟩
  refine ⟨P, ⟨v, hvnorm, rfl⟩, ?_⟩
  intro R
  let D := mat R.1
  have hD := mat_psd R
  let p := hD.isHermitian.eigenvalues
  let u : Fin 2 → EuclideanSpace ℂ (Fin 2) := hD.isHermitian.eigenvectorBasis
  have hsum : D = ∑ i, p i • ray (u i) :=
    D5.S3.Quantum.Matrix.CartesianVariance.hermitian_spectral_sum D hD.isHermitian
  have hp1 : ∑ i, p i = 1 :=
    D5.S3.Quantum.Matrix.CartesianVariance.density_eigenvalues_sum D ⟨hD, R.2.2⟩
  let lift : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2 × E) (Fin 2 × E) ℂ :=
    (Matrix.kroneckerBilinear (R := ℝ) (α := ℂ)).flip (mat γ.1)
  have hprod : D ⊗ₖ mat γ.1 = ∑ i, p i • (ray (u i) ⊗ₖ mat γ.1) := by
    change lift D = ∑ i, p i • lift (ray (u i))
    rw [hsum, map_sum]
    simp only [map_smul]
  change ((D ⊗ₖ mat γ.1) * Z).trace.re ≤ f v
  rw [hprod, trace_score_sum]
  exact score_le_weighted_max p (fun i => f (u i)) (f v) hD.eigenvalues_nonneg hp1
    (fun i => Or.inr (hmax (show u i ∈ Metric.sphere 0 1 from by
      simpa [u] using hD.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i)))

private theorem maximal_gibbs_slope (B : Fin 2 → CStarMatrix E E ℂ)
    (hB : ∀ i, IsSelfAdjoint (B i)) (Z : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) :
    let m := max (Real.log (partitionFunction (B 0))) (Real.log (partitionFunction (B 1)))
    ∃ ρ : DensityState (Fin 2 × E),
      (∃ v : EuclideanSpace ℂ (Fin 2), ‖v‖ = 1 ∧
        mat (retainedMarginal ρ).1 = Matrix.vecMulVec v.ofLp (star v.ofLp)) ∧
      gibbsValue B ρ = m ∧
      ∀ τ, gibbsValue B τ = m → (mat τ.1 * Z).trace.re ≤ (mat ρ.1 * Z).trace.re := by
  dsimp only
  classical
  let γ := blockGibbs B hB
  let g := fun i => Real.log (partitionFunction (B i))
  let m := max (g 0) (g 1)
  let S := fun ρ : DensityState (Fin 2 × E) => (mat ρ.1 * Z).trace.re
  obtain ⟨_, hend, hface⟩ := reducing_qubit_gibbs_argmax B hB
  have hwin : ∃ i, g i = m := by
    rcases le_total (g 0) (g 1) with h | h
    · exact ⟨1, (max_eq_right h).symm⟩
    · exact ⟨0, (max_eq_left h).symm⟩
  by_cases hcommon : γ 0 = γ 1 ∧ g 0 = g 1
  · obtain ⟨P, hpure, hscore⟩ := product_score_max (γ 0) Z
    let ρ := fromLegacyDensityState
      (productState (toLegacyDensityState P) (toLegacyDensityState (γ 0)))
    have hP : retainedMarginal ρ = P := by
      simp [ρ, retainedMarginal, marginalRight_productState]
    have hρ : mat ρ.1 = mat P.1 ⊗ₖ mat (γ 0).1 := rfl
    have hg (i : Fin 2) : g i = m := by
      fin_cases i <;> simp [m, hcommon.2]
    refine ⟨ρ, by rw [hP]; exact hpure, (hface ρ).2 ⟨fun i => Or.inr (hg i),
      Or.inr ⟨hcommon.1, by rw [hP]; exact hρ⟩⟩, ?_⟩
    intro τ hτ
    have ht : mat τ.1 = mat (retainedMarginal τ).1 ⊗ₖ mat (γ 0).1 := by
      rcases ((hface τ).1 hτ).2 with ht | ht
      · let R := mat (retainedMarginal τ).1
        have hγ (i : Fin 2) : γ i = γ 0 := by
          fin_cases i
          · rfl
          · exact hcommon.1.symm
        change mat τ.1 = retainedBlock (fun i => (R i i).re • mat (γ i).1) at ht
        apply Matrix.ext
        rintro ⟨i, e⟩ ⟨j, f⟩
        rw [ht, block_apply]
        change _ = R i j * mat (γ 0).1 e f
        by_cases hij : i = j
        · subst j
          rw [ite_eq_left rfl, hγ, Matrix.smul_apply, Complex.real_smul,
            real_diagonal (retainedMarginal τ)]
        · have hzero : R i j = 0 := by
            change (∑ a : E, mat τ.1 (i, a) (j, a)) = 0
            rw [ht]
            simp [block_apply, hij]
          rw [ite_eq_right hij, hzero, zero_mul]
      · exact ht.2
    rw [ht, hρ]
    exact hscore _
  · let W := Finset.univ.filter (fun i => g i = m)
    have hW : W.Nonempty := hwin.imp (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    obtain ⟨i, hi, hscore⟩ := Finset.exists_max_image W (fun j => S (gibbsEndpoint B hB j)) hW
    have hi' := (Finset.mem_filter.mp hi).2
    let ρ := gibbsEndpoint B hB i
    refine ⟨ρ, by rw [(hend i hi').2]; exact basis_marginal_pure i, (hend i hi').1, ?_⟩
    intro τ hτ
    let P := mat (retainedMarginal τ).1
    let p := fun j => (P j j).re
    obtain ⟨hw, ht⟩ := (hface τ).1 hτ
    have hdiag : mat τ.1 = retainedBlock (fun j => p j • mat (γ j).1) := by
      rcases ht with ht | ⟨hγ, ht⟩
      · exact ht
      · have hne : g 0 ≠ g 1 := fun hg => hcommon ⟨hγ, hg⟩
        have hz : p 0 = 0 ∨ p 1 = 0 := by
          rcases hw 0 with h | h
          · exact Or.inl h
          rcases hw 1 with q | q
          · exact Or.inr q
          exact (hne (h.trans q.symm)).elim
        have hzero (j k : Fin 2) (hjk : j ≠ k) : P j k = 0 := by
          have hbound := D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound
            (mat_psd (retainedMarginal τ)) j k
          have hprod : p j * p k = 0 := by
            fin_cases j <;> fin_cases k
            · exact (hjk rfl).elim
            · rcases hz with h | h <;> simp [h]
            · rcases hz with h | h <;> simp [h]
            · exact (hjk rfl).elim
          change Complex.normSq (P j k) ≤ p j * p k at hbound
          rw [hprod] at hbound
          exact Complex.normSq_eq_zero.mp (le_antisymm hbound (Complex.normSq_nonneg _))
        change mat τ.1 = P ⊗ₖ mat (γ 0).1 at ht
        have hγall (j : Fin 2) : γ j = γ 0 := by
          fin_cases j
          · rfl
          · exact hγ.symm
        apply Matrix.ext
        rintro ⟨j, e⟩ ⟨k, f⟩
        rw [ht, block_apply]
        change P j k * mat (γ 0).1 e f = _
        by_cases hjk : j = k
        · subst k
          rw [ite_eq_left rfl, hγall j, Matrix.smul_apply, Complex.real_smul]
          exact congrArg (fun x => x * mat (γ 0).1 e f) (real_diagonal (retainedMarginal τ) j).symm
        · rw [ite_eq_right hjk, hzero j k hjk, zero_mul]
    change (mat τ.1 * Z).trace.re ≤ S ρ
    rw [hdiag, endpoint_sum, trace_score_sum]
    exact score_le_weighted_max p (fun j => S (gibbsEndpoint B hB j)) (S ρ)
      (fun j => (Complex.nonneg_iff.mp ((mat_psd (retainedMarginal τ)).diag_nonneg (i := j))).1)
      (populations_sum τ) (fun j => (hw j).imp_right (fun hj =>
        hscore j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)))

/-- The joint observable whose expectation is the ordinary Petz residual score. -/
def ordinaryPetzResidual (σ : DensityState (Fin 2 × E)) (Y : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) :
    Matrix (Fin 2 × E) (Fin 2 × E) ℂ :=
  let S := mpow (mat σ.1) (1 / 2)
  let W := mpow (partialTraceRight (mat σ.1)) (-(1 / 2))
  Y - ((W * partialTraceRight (S * Y * S) * W) ⊗ₖ (1 : Matrix E E ℂ))

/-- The score of a physical trial against its ordinary Petz recovery. -/
def ordinaryPetzScore (σ : DensityState (Fin 2 × E)) (Y : Matrix (Fin 2 × E) (Fin 2 × E) ℂ)
    (ρ : DensityState (Fin 2 × E)) : ℝ :=
  ((mat ρ.1 - BKMFlagRefinement.partialTracePetz (mat σ.1) (mat (retainedMarginal ρ).1)) *
    Y).trace.re

/-- The log-reference pencil for the ordinary Petz score, Hermitian when `Y` is Hermitian. -/
def ordinaryPetzField (σ : DensityState (Fin 2 × E)) (Y : Matrix (Fin 2 × E) (Fin 2 × E) ℂ)
    (s : ℝ) : Matrix (Fin 2 × E) (Fin 2 × E) ℂ :=
  CFC.log (mat σ.1) - (CFC.log (mat (retainedMarginal σ).1) ⊗ₖ (1 : Matrix E E ℂ)) +
    s • ordinaryPetzResidual σ Y

private theorem ordinaryPetzScore_eq_trace (σ : DensityState (Fin 2 × E))
    (Y : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (ρ : DensityState (Fin 2 × E)) :
    ordinaryPetzScore σ Y ρ = (mat ρ.1 * ordinaryPetzResidual σ Y).trace.re := by
  let S := mpow (mat σ.1) (1 / 2)
  let W := mpow (partialTraceRight (mat σ.1)) (-(1 / 2))
  let P := mat (retainedMarginal ρ).1
  let T := (W * P * W) ⊗ₖ (1 : Matrix E E ℂ)
  have hadj : (S * T * S * Y).trace =
      (mat ρ.1 * ((W * partialTraceRight (S * Y * S) * W) ⊗ₖ (1 : Matrix E E ℂ))).trace := by
    calc
      _ = ((S * T) * (S * Y)).trace := by rw [Matrix.mul_assoc (S * T)]
      _ = (T * (S * Y * S)).trace := by
        rw [Matrix.mul_assoc S, Matrix.trace_mul_comm S, Matrix.mul_assoc T]
      _ = ((S * Y * S) * T).trace := Matrix.trace_mul_comm _ _
      _ = (partialTraceRight (S * Y * S) * (W * P * W)).trace :=
        trace_tensor_identity _ _
      _ = (P * (W * partialTraceRight (S * Y * S) * W)).trace := by
        let L := partialTraceRight (S * Y * S)
        change (L * (W * P * W)).trace = (P * (W * L * W)).trace
        calc
          _ = (W * (L * W * P)).trace := by
            rw [← Matrix.mul_assoc L, Matrix.trace_mul_comm _ W,
              Matrix.mul_assoc L W P]
          _ = ((W * L * W) * P).trace := by simp only [Matrix.mul_assoc]
          _ = _ := Matrix.trace_mul_comm _ _
      _ = _ := (trace_tensor_identity _ _).symm
  unfold ordinaryPetzScore ordinaryPetzResidual BKMFlagRefinement.partialTracePetz
    BKMFlagRefinement.lift
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  exact congrArg (fun x => (mat ρ.1 * Y).trace.re - x.re) hadj

private theorem ordinaryPetzValue_eq_gibbs (σ : DensityState (Fin 2 × E))
    (Y : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (r : ℝ)
    (B : Fin 2 → CStarMatrix E E ℂ)
    (hred : ordinaryPetzField σ Y r = retainedBlock (fun i => mat (B i)))
    (ρ : DensityState (Fin 2 × E)) :
    r * ordinaryPetzScore σ Y ρ - conditionalLoss ρ σ = gibbsValue B ρ := by
  rw [ordinaryPetzScore_eq_trace]
  unfold gibbsValue conditionalLoss
  rw [entropy_cross, entropy_cross, ← hred]
  unfold ordinaryPetzField
  rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, Complex.add_re, Complex.sub_re, trace_tensor_identity]
  rw [show partialTraceRight (mat ρ.1) = mat (retainedMarginal ρ).1 from rfl]
  simp only [Complex.smul_re, smul_eq_mul]
  ring

/-- In a basis reducing the ordinary Petz field at `r`, a physical state with a pure retained
marginal attains the full value and the largest score among all optimizers. Its affine
supporting line obeys the quadratic bound furnished by a score-loss inequality on that
trial. The loss has its Umegaki interpretation under the support conditions in
`conditionalLoss`, in particular on a faithful joint and retained reference. -/
theorem ordinary_petz_reducing_supporting_line
    (σ : DensityState (Fin 2 × E)) (Y : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (r : ℝ)
    (B : Fin 2 → CStarMatrix E E ℂ) (hB : ∀ i, IsSelfAdjoint (B i))
    (hred : ordinaryPetzField σ Y r = retainedBlock (fun i => mat (B i))) :
    let m := max (Real.log (partitionFunction (B 0))) (Real.log (partitionFunction (B 1)))
    let z := ordinaryPetzScore σ Y
    let F := fun t ρ => t * z ρ - conditionalLoss ρ σ
    ∃ ρ : DensityState (Fin 2 × E),
      (∃ v : EuclideanSpace ℂ (Fin 2), ‖v‖ = 1 ∧
        mat (retainedMarginal ρ).1 = Matrix.vecMulVec v.ofLp (star v.ofLp)) ∧
      F r ρ = m ∧ (∀ τ, F r τ ≤ m) ∧
      (∀ τ, F r τ = m → z τ ≤ z ρ) ∧
      (∀ s, F s ρ = m + (s - r) * z ρ) ∧
      ∀ C : ℝ, 0 < C → z ρ ^ 2 ≤ C * conditionalLoss ρ σ →
        ∀ s, m + (s - r) * z ρ ≤ C * s ^ 2 / 4 := by
  dsimp only
  let g := fun i => Real.log (partitionFunction (B i))
  let m := max (g 0) (g 1)
  obtain ⟨ρ, hpure, hvalue, hslope⟩ := maximal_gibbs_slope B hB (ordinaryPetzResidual σ Y)
  have hmax := (reducing_qubit_gibbs_argmax B hB).1
  have hopt : r * ordinaryPetzScore σ Y ρ - conditionalLoss ρ σ = m :=
    (ordinaryPetzValue_eq_gibbs σ Y r B hred ρ).trans hvalue
  have hline (s : ℝ) : s * ordinaryPetzScore σ Y ρ - conditionalLoss ρ σ =
      m + (s - r) * ordinaryPetzScore σ Y ρ := by rw [← hopt]; ring
  refine ⟨ρ, hpure, hopt, ?_, ?_, hline, ?_⟩
  · intro τ
    rw [ordinaryPetzValue_eq_gibbs σ Y r B hred]
    exact hmax.2 ⟨τ, rfl⟩
  · intro τ hτ
    simp only [ordinaryPetzScore_eq_trace]
    exact hslope τ ((ordinaryPetzValue_eq_gibbs σ Y r B hred τ).symm.trans hτ)
  · intro C hC hscore s
    rw [← hline]
    have hsq := sq_nonneg (ordinaryPetzScore σ Y ρ - C * s / 2)
    apply le_of_mul_le_mul_left _ hC
    nlinarith only [hsq, hscore]

#print axioms ordinary_petz_reducing_supporting_line

end D5.S3.Quantum.Recovery.QubitGibbsDeficit
