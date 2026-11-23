/- GID: D5/S3/Quantum/Recovery/QubitGibbsDeficit
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/QubitGibbsDeficit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact reducing qubit Gibbs deficit splits into conditional relative entropy loss and weighted block gaps. -/

import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import D5.S3.Quantum.Divergence.LegacyRelativeEntropyBoundary
import D5.S3.Quantum.Recovery.BKMFlagRefinement
import D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.QubitGibbsDeficit

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Divergence.LegacyRelativeEntropyBoundary
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
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

/-- The loss of Umegaki relative entropy under the physical partial trace. -/
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

end D5.S3.Quantum.Recovery.QubitGibbsDeficit
