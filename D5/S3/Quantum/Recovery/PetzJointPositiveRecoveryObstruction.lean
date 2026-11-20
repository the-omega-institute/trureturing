import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import D5.S3.Quantum.Matrix.PartialTransposeTrace
import D5.S3.Quantum.QuantumChannels.RealPartPositiveObstruction
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness

/-!
# Six-state obstruction to common CPTP recovery after transposition

For the six faithful Pauli perturbations of the maximally mixed qubit, the
finite Umegaki entropy loss is zero. The minimum worst-case full trace norm
of recovery is `2 * ε / 3`, attained by the equal Pauli mixture of I, X and Z.
-/

set_option autoImplicit false

noncomputable section

namespace PetzJointPositiveRecoveryObstruction

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm traceNorm_eq_max_re_tr_U)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (finiteTraceLogRelativeEntropy SupportContained support_of_posDef)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli pauli_zero pauli_one pauli_two)
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsCPTP)
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
  (pauliChannel channel_cptp sigma sigma_properties)
open D5.S3.Quantum.QuantumChannels.RealPartPositiveObstruction (antisymmetric)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Matrix.PartialTransposeTrace (partial_transpose_trace_duality)

abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ
abbrev QubitMap := MatrixMap (Fin 2) (Fin 2) ℂ

abbrev transposeMap (n : Type*) : MatrixMap n n ℂ :=
  (Matrix.transposeLinearEquiv n n ℂ ℂ).toLinearMap

theorem transposeMap_positive_tp (n : Type*) [Fintype n] :
    (transposeMap n).IsPositive ∧ (transposeMap n).IsTracePreserving := by
  constructor
  · intro A hA
    exact hA.transpose
  · intro A
    exact Matrix.trace_transpose A

def reference : Qubit := (1 / 2 : ℂ) • 1

def signedPauli (j : Fin 3) (s : Bool) : Qubit :=
  if s then pauli j else -pauli j

/-- The three axes and two signs give the six Pauli perturbations. -/
def probe (ε : ℝ) (j : Fin 3) (s : Bool) : Qubit :=
  reference + ((ε : ℂ) / 2) • signedPauli j s

private theorem pauli_adjoint_square (j : Fin 3) :
    (pauli j)ᴴ = pauli j ∧ pauli j * pauli j = 1 := by
  fin_cases j
  · exact sigma_properties 1
  · exact sigma_properties 2
  · exact sigma_properties 3

private theorem signedPauli_adjoint (j : Fin 3) (s : Bool) :
    (signedPauli j s)ᴴ = signedPauli j s := by
  cases s <;> simp [signedPauli, (pauli_adjoint_square j).1]

private theorem signedPauli_square (j : Fin 3) (s : Bool) :
    signedPauli j s * signedPauli j s = 1 := by
  cases s <;> simp [signedPauli, (pauli_adjoint_square j).2]

private theorem signedPauli_trace (j : Fin 3) (s : Bool) :
    (signedPauli j s).trace = 0 := by
  cases s <;> fin_cases j <;>
    norm_num [signedPauli, pauli_zero, pauli_one, pauli_two, Matrix.trace_fin_two]

theorem probe_trace (ε : ℝ) (j : Fin 3) (s : Bool) : (probe ε j s).trace = 1 := by
  norm_num [probe, reference, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    signedPauli_trace]

theorem probe_posDef {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) (j : Fin 3) (s : Bool) :
    (probe ε j s).PosDef := by
  let P := signedPauli j s
  let B : Qubit := 1 + P
  have hB : Bᴴ * B = (2 : ℂ) • (1 + P) := by
    simp only [B, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      show Pᴴ = P from signedPauli_adjoint j s, Matrix.add_mul, Matrix.mul_add,
      one_mul, mul_one, show P * P = 1 from signedPauli_square j s]
    module
  have hsplit : probe ε j s =
      (((1 - ε) / 2 : ℝ) : ℂ) • (1 : Qubit) + ((ε / 4 : ℝ) : ℂ) • (Bᴴ * B) := by
    rw [hB]
    change (1 / 2 : ℂ) • (1 : Qubit) + ((ε : ℂ) / 2) • P = _
    push_cast
    rw [smul_smul, smul_add]
    module
  rw [hsplit]
  exact (Matrix.PosDef.one.smul
    (Complex.zero_lt_real.mpr (by linarith : 0 < (1 - ε) / 2))).add_posSemidef
    ((Matrix.posSemidef_conjTranspose_mul_self B).smul
      (Complex.zero_le_real.mpr (by linarith : 0 ≤ ε / 4)))

/-- The repository Choi convention places the output index first. -/
private theorem choi_after_transpose (R : QubitMap) :
    partialTranspose (MatrixMap.choi_matrix (R.comp (transposeMap (Fin 2)))) =
      MatrixMap.choi_matrix R := by
  ext ⟨a, i⟩ ⟨b, j⟩
  change R ((Matrix.single j i (1 : ℂ)).transpose) a b =
    R (Matrix.single i j 1) a b
  rw [Matrix.transpose_single]

private abbrev singlet : Fin 2 × Fin 2 → ℂ := antisymmetric 0 1

/-- The trace test is the partial transpose of the outer product of the
unnormalized antisymmetric vector from `RealPartPositiveObstruction`. -/
def choiWitness : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  partialTranspose (Matrix.vecMulVec singlet (star singlet))

private theorem apply_from_choi (F : QubitMap) (A : Qubit) (a b : Fin 2) :
    F A a b =
      A 0 0 * F.choi_matrix (a, 0) (b, 0) +
      A 0 1 * F.choi_matrix (a, 0) (b, 1) +
      (A 1 0 * F.choi_matrix (a, 1) (b, 0) +
       A 1 1 * F.choi_matrix (a, 1) (b, 1)) := by
  have h := congrArg (fun G : QubitMap => G A a b) (MatrixMap.choi_map_inv F)
  change (∑ i : Fin 2, ∑ j : Fin 2, A i j * F.choi_matrix (a, i) (b, j)) = F A a b at h
  simpa only [Fin.sum_univ_two] using h.symm

set_option maxHeartbeats 3000000 in
-- Expanding the three Pauli trace pairings requires normalizing complex matrix entries.
/-- The exact Choi trace identity for any complex-linear qubit map. -/
theorem choi_witness_identity (F : QubitMap) :
    (F.choi_matrix * choiWitness).trace =
      ((F 1).trace - ∑ j : Fin 3, (pauli j * F (pauli j)).trace) / 2 := by
  rw [choiWitness, ← partial_transpose_trace_duality]
  simp only [Fin.sum_univ_three, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  simp only [apply_from_choi]
  apply Complex.ext <;>
    norm_num [partialTranspose, singlet, antisymmetric, Pi.single_apply, Pi.star_apply,
      Pi.sub_apply, Prod.mk.injEq, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply, pauli_zero, pauli_one, pauli_two,
      Complex.star_def, div_eq_mul_inv, Complex.inv_re, Complex.inv_im,
      Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im] <;> ring

def pauliReadout (F : QubitMap) (j : Fin 3) : ℝ :=
  ((pauli j * F (pauli j)).trace).re

/-- Complete positivity bounds the sum of the three target-axis readouts.
Here `F = R ∘ transposeMap`, so the transposition signs are in the inputs. -/
theorem choi_readout_bound (R : QubitMap) (hR : IsCPTP R) :
    ∑ j : Fin 3, pauliReadout (R.comp (transposeMap (Fin 2))) j ≤ 2 := by
  let F := R.comp (transposeMap (Fin 2))
  have hChoi := (MatrixMap.choi_PSD_iff_CP_map R).mp hR.1
  have hq : 0 ≤ star singlet ⬝ᵥ (partialTranspose (MatrixMap.choi_matrix F) *ᵥ singlet) := by
    rw [show partialTranspose (MatrixMap.choi_matrix F) = R.choi_matrix from choi_after_transpose R]
    exact hChoi.dotProduct_mulVec_nonneg singlet
  rw [partial_transpose_trace_duality] at hq
  change 0 ≤ (MatrixMap.choi_matrix F * choiWitness).trace at hq
  rw [choi_witness_identity] at hq
  have htrace : (F 1).trace = 2 := by
    change (R ((1 : Qubit).transpose)).trace = 2
    rw [Matrix.transpose_one, hR.2]
    norm_num [Matrix.trace_one]
  rw [htrace] at hq
  have hsum : (∑ j : Fin 3, (pauli j * F (pauli j)).trace).re =
      ∑ j : Fin 3, pauliReadout F j := by
    simp [Fin.sum_univ_three, pauliReadout]
  have hreal : 0 ≤ (2 - ∑ j : Fin 3, pauliReadout F j) * (1 / 2 : ℝ) := by
    have h := (Complex.nonneg_iff.mp hq).1
    norm_num [div_eq_mul_inv, Complex.mul_re, Complex.sub_re, Complex.inv_re,
      Complex.inv_im, Complex.normSq, hsum] at h ⊢
    exact h
  change ∑ j : Fin 3, pauliReadout F j ≤ 2
  linarith only [hreal]

private def signedUnitary (j : Fin 3) (s : Bool) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨signedPauli j s, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, signedPauli_adjoint, signedPauli_square])⟩

private theorem signed_readout_le_norm (D : Qubit) (j : Fin 3) (s : Bool) :
    ((signedPauli j s * D).trace).re ≤ traceNorm D :=
  (traceNorm_eq_max_re_tr_U D).2 ⟨signedUnitary j s, rfl⟩

private def residual (F : QubitMap) (ε : ℝ) (j : Fin 3) (s : Bool) : Qubit :=
  probe ε j s - F (probe ε j s)

private theorem residual_pair (F : QubitMap) (ε : ℝ) (j : Fin 3) :
    residual F ε j true - residual F ε j false =
      (ε : ℂ) • (pauli j - F (pauli j)) := by
  simp only [residual, probe, signedPauli, ite_true, Bool.false_eq_true, ite_false,
    map_add, map_smul, map_neg]
  module

/-- Full trace norm of the difference between the recovered state and target. -/
def recoveryError (ε : ℝ) (R : QubitMap) (i : Fin 3 × Bool) : ℝ :=
  traceNorm (probe ε i.1 i.2 - R (transposeMap (Fin 2) (probe ε i.1 i.2)))

/-- The finite maximum over the three axes and both signs. -/
def worstError (ε : ℝ) (R : QubitMap) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (recoveryError ε R)

private theorem error_le_worst (ε : ℝ) (R : QubitMap) (i : Fin 3 × Bool) :
    recoveryError ε R i ≤ worstError ε R :=
  Finset.le_sup' (recoveryError ε R) (Finset.mem_univ i)

theorem worstError_lower_bound {ε : ℝ} (hε : 0 < ε) (R : QubitMap)
    (hR : IsCPTP R) : 2 * ε / 3 ≤ worstError ε R := by
  let F := R.comp (transposeMap (Fin 2))
  have hsum : ∑ j : Fin 3, pauliReadout F j ≤ 2 := choi_readout_bound R hR
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, pauliReadout F j ≤ 2 / 3 := by
    by_contra! h
    rw [Fin.sum_univ_three] at hsum
    linarith only [hsum, h 0, h 1, h 2]
  have hplus :
      ((pauli j * residual F ε j true).trace).re ≤ worstError ε R :=
    (signed_readout_le_norm _ j true).trans (error_le_worst ε R (j, true))
  have hminus :
      -((pauli j * residual F ε j false).trace).re ≤ worstError ε R := by
    simpa only [signedPauli, Bool.false_eq_true, ite_false, Matrix.neg_mul,
      Matrix.trace_neg, Complex.neg_re] using
      (signed_readout_le_norm (residual F ε j false) j false).trans
        (error_le_worst ε R (j, false))
  have hpair :
      ((pauli j * residual F ε j true).trace).re -
        ((pauli j * residual F ε j false).trace).re =
        ε * (2 - pauliReadout F j) := by
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.mul_sub, residual_pair,
      Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, (pauli_adjoint_square j).2,
      Matrix.trace_sub]
    norm_num [pauliReadout, Matrix.trace_one, smul_eq_mul, Complex.mul_re]
  have hsize : ε * (2 - (2 / 3 : ℝ)) ≤ ε * (2 - pauliReadout F j) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hj 2) hε.le
  linarith only [hplus, hminus, hpair, hsize]

private def mixtureWeights : Fin 4 → ℝ := ![1 / 3, 1 / 3, 0, 1 / 3]

/-- Equal mixture of identity, Pauli X conjugation and Pauli Z conjugation. -/
def optimalRecovery : QubitMap := pauliChannel mixtureWeights

theorem optimalRecovery_cptp : IsCPTP optimalRecovery := by
  change IsCPTP (pauliChannel mixtureWeights)
  apply channel_cptp
  · intro j
    fin_cases j <;> norm_num [mixtureWeights]
  · norm_num [mixtureWeights, Fin.sum_univ_four]

theorem optimalRecovery_apply (A : Qubit) :
    optimalRecovery A = (1 / 3 : ℂ) • (A.transpose + A.trace • (1 : Qubit)) := by
  have hI : sigma 0 = (1 : Qubit) := rfl
  have hX : sigma 1 = pauli 0 := rfl
  have hZ : sigma 3 = pauli 2 := rfl
  change (∑ j : Fin 4, (mixtureWeights j : ℂ) • (sigma j * A * sigma j)) = _
  simp only [Fin.sum_univ_four, hI, hX, hZ, one_mul, mul_one, pauli_zero, pauli_two]
  norm_num [mixtureWeights]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [mixtureWeights, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.trace_fin_two,
      Matrix.transpose_apply, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul] <;> ring

/-- The optimizer's actual output on every transposed probe. -/
theorem optimalRecovery_output (ε : ℝ) (j : Fin 3) (s : Bool) :
    optimalRecovery (transposeMap (Fin 2) (probe ε j s)) =
      reference + ((ε : ℂ) / 6) • signedPauli j s := by
  rw [optimalRecovery_apply]
  change (1 / 3 : ℂ) •
    ((probe ε j s).transpose.transpose + (probe ε j s).transpose.trace • (1 : Qubit)) = _
  rw [Matrix.transpose_transpose, Matrix.trace_transpose, probe_trace]
  simp only [probe, reference, one_smul]
  module

private theorem traceNorm_signedPauli (j : Fin 3) (s : Bool) :
    traceNorm (signedPauli j s) = 2 := by
  norm_num [traceNorm, signedPauli_adjoint, signedPauli_square, Matrix.trace_one]

theorem optimalRecovery_error {ε : ℝ} (hε : 0 ≤ ε) (i : Fin 3 × Bool) :
    recoveryError ε optimalRecovery i = 2 * ε / 3 := by
  rcases i with ⟨j, s⟩
  have hres :
      residual (optimalRecovery.comp (transposeMap (Fin 2))) ε j s =
        ((ε / 3 : ℝ) : ℂ) • signedPauli j s := by
    change probe ε j s - optimalRecovery (transposeMap (Fin 2) (probe ε j s)) = _
    rw [optimalRecovery_output]
    unfold probe
    push_cast
    module
  change traceNorm (residual (optimalRecovery.comp (transposeMap (Fin 2))) ε j s) = _
  rw [hres, traceNorm_smul_nonneg _ _ (by positivity), traceNorm_signedPauli]
  ring

theorem optimalRecovery_worstError {ε : ℝ} (hε : 0 ≤ ε) :
    worstError ε optimalRecovery = 2 * ε / 3 := by
  unfold worstError
  simp only [optimalRecovery_error hε, Finset.sup'_const]

/-- The minimum is attained among all completely positive trace-preserving maps. -/
theorem six_state_minimax {ε : ℝ} (hε : 0 < ε) :
    IsLeast {r : ℝ | ∃ R : QubitMap, IsCPTP R ∧ worstError ε R = r}
      (2 * ε / 3) := by
  refine ⟨⟨optimalRecovery, optimalRecovery_cptp, optimalRecovery_worstError hε.le⟩, ?_⟩
  rintro r ⟨R, hR, rfl⟩
  exact worstError_lower_bound hε R hR

theorem six_state_minimax_value {ε : ℝ} (hε : 0 < ε) :
    sInf {r : ℝ | ∃ R : QubitMap, IsCPTP R ∧ worstError ε R = r} = 2 * ε / 3 :=
  (six_state_minimax hε).csInf_eq

theorem no_common_cptp_inverse {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ R : QubitMap, IsCPTP R ∧
      ∀ j s, R (transposeMap (Fin 2) (probe ε j s)) = probe ε j s := by
  rintro ⟨R, hR, hExact⟩
  have hZero : worstError ε R ≤ 0 := by
    unfold worstError
    apply Finset.sup'_le
    rintro ⟨j, s⟩ _
    change traceNorm (probe ε j s - R (transposeMap (Fin 2) (probe ε j s))) ≤ 0
    rw [hExact j s, sub_self]
    simp [traceNorm]
  linarith only [hε, (worstError_lower_bound hε R hR).trans hZero]

section Entropy

variable {n : Type*} [Fintype n] [DecidableEq n]

private abbrev raw (ρ : DensityState n) : Matrix n n ℂ :=
  CStarMatrix.ofMatrix.symm ρ.1

private theorem raw_psd (ρ : DensityState n) : (raw ρ).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)

private def densityOfMatrix (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (htr : A.trace = 1) : DensityState n :=
  ⟨CStarMatrix.ofMatrix A, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hA.nonneg, htr⟩

def transposeState (ρ : DensityState n) : DensityState n :=
  densityOfMatrix ((raw ρ).transpose)
    ((transposeMap_positive_tp n).1 (raw_psd ρ))
    (((transposeMap_positive_tp n).2 (raw ρ)).trans ρ.2.2)

theorem transposeState_matrix (ρ : DensityState n) :
    CStarMatrix.ofMatrix.symm (transposeState ρ).1 =
      transposeMap n (CStarMatrix.ofMatrix.symm ρ.1) := rfl

private theorem cfc_transpose_of_hermitian {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A.transpose = (cfc f A).transpose := by
  let U := hA.eigenvectorUnitary
  let V := Matrix.UnitaryGroup.transpose (star U)
  have hV : V.val = (star U.val).transpose := rfl
  have hVstar : star V.val = U.val.transpose := by
    simp only [hV, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  have hD : A = U.val * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U.val := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Unitary.coe_star] using hA.spectral_theorem
  have hDT : A.transpose =
      V.val * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star V.val := by
    rw [hVstar, hV]
    simpa only [Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.mul_assoc] using congrArg Matrix.transpose hD
  rw [hA.transpose.cfc_eq f, hA.cfc_eq f,
    hA.transpose.cfc_eq_any_unitary hDT f, hA.cfc_eq_any_unitary hD f]
  rw [hVstar, hV]
  simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

private theorem raw_log (ρ : DensityState n) :
    CStarMatrix.ofMatrix (cfc Real.log (raw ρ)) = CFC.log ρ.1 := by
  exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log (raw ρ)
    ((raw ρ).finite_real_spectrum.continuousOn _)
    CStarMatrix.ofMatrixL.continuous (raw_psd ρ).isHermitian
    (by exact (raw_psd ρ).isHermitian)

private theorem entropy_as_matrix_trace (ρ σ : DensityState n) :
    finiteTraceLogRelativeEntropy ρ σ =
      ((raw ρ * (cfc Real.log (raw ρ) - cfc Real.log (raw σ))).trace).re := by
  unfold finiteTraceLogRelativeEntropy
  rw [← raw_log ρ, ← raw_log σ]
  rfl

/-- Simultaneous transposition preserves the finite trace-log value. A
faithful reference makes this the Umegaki relative entropy for every state. -/
theorem finiteTraceLog_transpose (ρ σ : DensityState n) :
    finiteTraceLogRelativeEntropy (transposeState ρ) (transposeState σ) =
      finiteTraceLogRelativeEntropy ρ σ := by
  rw [entropy_as_matrix_trace, entropy_as_matrix_trace]
  change ((raw ρ).transpose *
    (cfc Real.log (raw ρ).transpose - cfc Real.log (raw σ).transpose)).trace.re =
      ((raw ρ * (cfc Real.log (raw ρ) - cfc Real.log (raw σ))).trace).re
  rw [cfc_transpose_of_hermitian (raw_psd ρ).isHermitian,
    cfc_transpose_of_hermitian (raw_psd σ).isHermitian,
    ← Matrix.transpose_sub, Matrix.trace_transpose_mul]

end Entropy

theorem reference_posDef : reference.PosDef := by
  exact Matrix.PosDef.one.smul (by norm_num [Complex.lt_def])

def referenceState : DensityState (Fin 2) :=
  densityOfMatrix reference reference_posDef.posSemidef
    (by norm_num [reference, Matrix.trace_smul, Matrix.trace_one])

def probeState {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) (j : Fin 3) (s : Bool) :
    DensityState (Fin 2) :=
  densityOfMatrix (probe ε j s) (probe_posDef hε hε₁ j s).posSemidef (probe_trace ε j s)

theorem transpose_reference : transposeMap (Fin 2) reference = reference := by
  change reference.transpose = reference
  simp [reference, Matrix.transpose_smul]

theorem retained_commutes_reference (ε : ℝ) (j : Fin 3) (s : Bool) :
    Commute (transposeMap (Fin 2) (probe ε j s)) (transposeMap (Fin 2) reference) := by
  rw [transpose_reference]
  exact (Commute.one_right _).smul_right (1 / 2 : ℂ)

theorem transposed_probe_faithful {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    (j : Fin 3) (s : Bool) :
    (transposeMap (Fin 2) (probe ε j s)).PosDef :=
  (probe_posDef hε hε₁ j s).transpose

/-- The finite Umegaki loss on the two actual positive-map outputs is zero. -/
theorem probe_zero_entropy_loss {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    (j : Fin 3) (s : Bool) :
    let ρ := probeState hε hε₁ j s
    let σ := referenceState
    SupportContained ρ σ ∧ SupportContained (transposeState ρ) (transposeState σ) ∧
      finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (transposeState ρ) (transposeState σ) = 0 := by
  dsimp only
  refine ⟨support_of_posDef _ _ reference_posDef,
    support_of_posDef _ _ reference_posDef.transpose, ?_⟩
  rw [finiteTraceLog_transpose, sub_self]

/-- Transposition is itself one positive trace-preserving inverse on every input. -/
theorem transpose_recovers (A : Qubit) :
    transposeMap (Fin 2) (transposeMap (Fin 2) A) = A :=
  Matrix.transpose_transpose A

/-- The six faithful zero-loss inputs exhibit a strictly positive minimum
worst-case full trace error for a common CPTP inverse. -/
theorem six_state_zero_loss_obstruction {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    (∀ j s,
      (probe ε j s).PosDef ∧
      (transposeMap (Fin 2) (probe ε j s)).PosDef ∧
      Commute (transposeMap (Fin 2) (probe ε j s)) (transposeMap (Fin 2) reference) ∧
      finiteTraceLogRelativeEntropy (probeState hε hε₁ j s) referenceState -
        finiteTraceLogRelativeEntropy (transposeState (probeState hε hε₁ j s))
          (transposeState referenceState) = 0) ∧
    IsLeast {r : ℝ | ∃ R : QubitMap, IsCPTP R ∧ worstError ε R = r} (2 * ε / 3) := by
  refine ⟨?_, six_state_minimax hε⟩
  intro j s
  exact ⟨probe_posDef hε hε₁ j s, transposed_probe_faithful hε hε₁ j s,
    retained_commutes_reference ε j s, (probe_zero_entropy_loss hε hε₁ j s).2.2⟩

end PetzJointPositiveRecoveryObstruction
