/- GID: D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.claim; result=D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.result; claim=D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.claim
   digest: A two-qubit state is spatially steerable and temporally compatible. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Weil.ZetaLinear.RankTrace

/-! Spatial EPR steering and CPTP temporal compatibility for two-qubit operators. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

namespace D5.S3.Quantum.Contextuality.SteeringTemporalCompatibilityRefutation

/-- A positive, trace-one operator on two qubits. -/
def TwoQubitDensity (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  R.PosSemidef ∧ R.trace = 1

/-- Apply a qubit channel to the second tensor factor. -/
def applySecond (E : QuantumChannel (Fin 2) (Fin 2))
    (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => CStarMatrix.ofMatrix.symm
    (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix
      (fun b d => R (p.1, b) (q.1, d)))) p.2 q.2

/-- Equation (3): the anticommutator of the first marginal with the swap. -/
def temporalKernel (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let S := D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap 2
  let A := partialTraceRight R ⊗ₖ ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
  A * S + S * A

/-- Compatibility with a CPTP temporal mechanism from the first qubit to the second. -/
def TemporalForward (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  ∃ E : QuantumChannel (Fin 2) (Fin 2), R = applySecond E (temporalKernel R)

/-- Compatibility in the reverse direction, interchanging the tensor factors. -/
def TemporalReverse (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  TemporalForward (R.submatrix Prod.swap Prod.swap)

/-- Neither temporal direction admits a quantum channel. -/
def Atemporal (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  ¬ TemporalForward R ∧ ¬ TemporalReverse R

/-- A finite family of two-outcome projective measurements. -/
def BinaryProjective {n : ℕ} (P : Fin n → Bool → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ x b, (P x b).IsHermitian ∧ P x b * P x b = P x b) ∧
    ∀ x, P x false + P x true = 1

/-- The unnormalized conditional state on the first qubit after measuring the second. -/
def assemblage {n : ℕ} (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (P : Fin n → Bool → Matrix (Fin 2) (Fin 2) ℂ) :
    Fin n → Bool → Matrix (Fin 2) (Fin 2) ℂ :=
  fun x b => partialTraceRight ((1 ⊗ₖ P x b) * R)

/-- A local-hidden-state model indexed by all deterministic response functions. -/
def HasLHS {n : ℕ} (σ : Fin n → Bool → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ H : (Fin n → Bool) → Matrix (Fin 2) (Fin 2) ℂ,
    (∀ lam, (H lam).PosSemidef) ∧
      ∀ x b, (∑ lam, if lam x = b then H lam else 0) = σ x b

/-- Some finite projective measurement family on the second qubit has no LHS model. -/
def SteerableBA (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  ∃ n : ℕ, ∃ P : Fin n → Bool → Matrix (Fin 2) (Fin 2) ℂ,
    BinaryProjective P ∧ ¬ HasLHS (assemblage R P)

/-- Steering in the other direction. -/
def SteerableAB (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  SteerableBA (R.submatrix Prod.swap Prod.swap)

/-- The steering implication in the discussion of Song et al., arXiv:2306.09336v2. -/
def claim : Prop :=
  ∀ R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
    TwoQubitDensity R → (SteerableBA R ∨ SteerableAB R) → Atemporal R

private def stateR : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => (!![!![5391, 0; 0, 3609], !![0, 1782; 1188, 0];
    !![0, 1188; 1782, 0], !![401, 0; 0, 599]] :
      Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ)) p.1 q.1 p.2 q.2 / 10000

private def marginalA : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![9 / 10, 1 / 10]

private theorem state_marginal : partialTraceRight stateR = marginalA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceRight, stateR, marginalA, diagonal, Fin.sum_univ_two]

private def measurements : Fin 2 → Bool → Matrix (Fin 2) (Fin 2) ℂ :=
  fun x b => (1 / 2 : ℂ) •
    (1 + (if b then (-1 : ℂ) else 1) • pauliMatrix (if x = 0 then .X else .Z))

private def witnessC : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 9, 0; 0, 1]
private def witnessU : Matrix (Fin 2) (Fin 2) ℂ :=
  !![20 / 909, 33 / 101; 33 / 101, -20 / 101]
private def witnessV : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-20 / 909, 33 / 101; 33 / 101, 20 / 101]

private def steeringScore (σ : Fin 2 → Bool → Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (witnessU * ((σ 0 false - σ 0 true) + (σ 1 false - σ 1 true)) +
    witnessV * ((σ 0 false - σ 0 true) - (σ 1 false - σ 1 true))).trace.re

private def quantumAssemblage : Fin 2 → Bool → Matrix (Fin 2) (Fin 2) ℂ :=
  fun x b => if x = 0 then
    !![9 / 20, (if b then -297 else 297) / 2000;
      (if b then -297 else 297) / 2000, 1 / 20]
  else if b then !![3609 / 10000, 0; 0, 599 / 10000]
  else !![5391 / 10000, 0; 0, 401 / 10000]

private theorem quantum_assemblage : assemblage stateR measurements = quantumAssemblage := by
  funext x b
  ext i j
  fin_cases x <;> cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [assemblage, partialTraceRight, measurements, quantumAssemblage,
      stateR, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      kroneckerMap_apply, pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ]

private def responseWitness (s t : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  if s = t then (if s then -witnessU else witnessU)
  else (if s then -witnessV else witnessV)

private theorem witness_domination (s t : Bool) :
    (witnessC - responseWitness s t).PosSemidef := by
  let q : Fin 2 → ℂ := if s then
    (if t then ![11 / 3, 9] else ![3, 11])
    else (if t then ![11 / 3, -9] else ![3, -11])
  have heq : witnessC - responseWitness s t =
      (1 / 101 : ℝ) • vecMulVec q (star q) := by
    cases s <;> cases t <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [witnessC, witnessU, witnessV, responseWitness, q, vecMulVec, map_ofNat]
  rw [heq]
  exact (posSemidef_vecMulVec_self_star q).smul (by norm_num : (0 : ℝ) ≤ 1 / 101)

private theorem state_density : TwoQubitDensity stateR := by
  let v : Fin 2 × Fin 2 → ℂ := fun p => if p = (0, 0) then 3 else
    if p = (1, 1) then 1 else 0
  let w : Fin 2 × Fin 2 → ℂ := fun p => if p = (0, 1) then 3 else
    if p = (1, 0) then 1 else 0
  have heq : stateR =
      (99 / 100 : ℝ) • ((3 / 50 : ℝ) • vecMulVec v (star v) +
        (1 / 25 : ℝ) • vecMulVec w (star w)) +
      (1 / 100 : ℝ) • (marginalA ⊗ₖ ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [stateR, marginalA, v, w, vecMulVec, kroneckerMap_apply, diagonal, map_ofNat]
  constructor
  · rw [heq]
    apply Matrix.PosSemidef.add
    · exact ((posSemidef_vecMulVec_self_star v).smul (by norm_num : (0 : ℝ) ≤ 3 / 50) |>.add
        ((posSemidef_vecMulVec_self_star w).smul (by norm_num : (0 : ℝ) ≤ 1 / 25))).smul
          (by norm_num : (0 : ℝ) ≤ 99 / 100)
    · apply Matrix.PosSemidef.smul _ (by norm_num : (0 : ℝ) ≤ 1 / 100)
      apply Matrix.PosSemidef.kronecker
      · apply Matrix.PosSemidef.diagonal
        intro i
        fin_cases i <;> norm_num [Complex.le_def]
      · exact Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · rw [← trace_partialTraceRight, state_marginal]
    norm_num [marginalA, Matrix.trace, Matrix.diag, diagonal, Fin.sum_univ_two]

private def channelWeights : Fin 4 → ℝ :=
  ![4183 / 10000, 3787 / 10000, 223 / 10000, 1807 / 10000]

private def pauliKraus (j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  Real.sqrt (channelWeights j) • pauliMatrix
    (D5.S3.Quantum.Information.SignedPauliSumNormRefutation.sigmaOfDigit j.val)

private def pauliAction (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ j : Fin 4, channelWeights j •
    (pauliMatrix (D5.S3.Quantum.Information.SignedPauliSumNormRefutation.sigmaOfDigit j.val) *
      M * (pauliMatrix
        (D5.S3.Quantum.Information.SignedPauliSumNormRefutation.sigmaOfDigit j.val)).conjTranspose)

private theorem channel_weights_nonnegative (j : Fin 4) : 0 ≤ channelWeights j := by
  fin_cases j <;> norm_num [channelWeights]

private theorem pauli_kraus_complete : (∑ j, (pauliKraus j).conjTranspose * pauliKraus j) = 1 := by
  have hterm (j : Fin 4) : (pauliKraus j).conjTranspose * pauliKraus j =
      channelWeights j • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp only [pauliKraus, Matrix.conjTranspose_smul, star_trivial,
      pauli_hermitian, smul_mul_smul, Real.mul_self_sqrt (channel_weights_nonnegative j),
      letter_mul]
    fin_cases j <;>
      simp [D5.S3.Quantum.Information.SignedPauliSumNormRefutation.sigmaOfDigit,
        letterPhase, letterProduct, pauliMatrix.eq_1]
  simp_rw [hterm]
  rw [← Finset.sum_smul]
  have hsum : (∑ j, channelWeights j) = 1 := by
    norm_num [channelWeights, Fin.sum_univ_succ]
  rw [hsum, one_smul]

private theorem pauli_kraus_action (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ j, pauliKraus j * M * (pauliKraus j).conjTranspose) = pauliAction M := by
  unfold pauliAction
  apply Finset.sum_congr rfl
  intro j _
  simp only [pauliKraus, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt (channel_weights_nonnegative j)]

private theorem pauli_action_entries (M : Matrix (Fin 2) (Fin 2) ℂ) : pauliAction M =
    !![(599 / 1000 : ℂ) * M 0 0 + (401 / 1000) * M 1 1,
       (297 / 1250) * M 0 1 + (891 / 2500) * M 1 0;
       (297 / 1250) * M 1 0 + (891 / 2500) * M 0 1,
       (401 / 1000) * M 0 0 + (599 / 1000) * M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliAction, channelWeights, Fin.sum_univ_succ,
      D5.S3.Quantum.Information.SignedPauliSumNormRefutation.sigmaOfDigit,
      pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, map_ofNat, Matrix.vecMul, dotProduct] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

private theorem temporal_certificate : stateR =
    Matrix.of (fun p q => pauliAction
      (Matrix.of fun b d => temporalKernel stateR (p.1, b) (q.1, d)) p.2 q.2) := by
  simp only [pauli_action_entries]
  unfold temporalKernel
  rw [state_marginal]
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [
      D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap,
      stateR, marginalA, diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, kroneckerMap_apply, map_ofNat,
      Matrix.one_apply, Matrix.submatrix_apply, Prod.swap, id_eq]

private theorem state_temporal : TemporalForward stateR := by
  obtain ⟨E, hE⟩ := finite_kraus_quantum_channel pauliKraus pauli_kraus_complete
  have haction (M : Matrix (Fin 2) (Fin 2) ℂ) :
      CStarMatrix.ofMatrix.symm (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)) =
        pauliAction M := (hE M).trans (pauli_kraus_action M)
  refine ⟨E, temporal_certificate.trans ?_⟩
  funext p q
  exact (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M p.2 q.2)
    (haction (fun b d => temporalKernel stateR (p.1, b) (q.1, d)))).symm

private theorem measurements_projective : BinaryProjective measurements := by
  constructor
  · intro x b
    constructor
    · change (measurements x b).conjTranspose = measurements x b
      simp only [measurements, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_one, pauli_hermitian]
      cases b <;> norm_num
    · fin_cases x <;> cases b <;>
        simp [measurements, Matrix.mul_add, Matrix.add_mul,
          smul_smul, letter_mul, letterPhase, letterProduct,
          pauliMatrix.eq_1] <;> module
  · intro x
    ext i j
    simp [measurements, Matrix.add_apply, Matrix.smul_apply]
    ring

private theorem deterministic_difference {ι : Type*} [Fintype ι]
    (H : ι → Matrix (Fin 2) (Fin 2) ℂ) (r : ι → Bool) :
    (∑ k, if r k = false then H k else 0) - (∑ k, if r k = true then H k else 0) =
      ∑ k, if r k then -H k else H k := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases r k <;> simp

private theorem deterministic_total {ι : Type*} [Fintype ι]
    (H : ι → Matrix (Fin 2) (Fin 2) ℂ) (r : ι → Bool) :
    (∑ k, if r k = false then H k else 0) + (∑ k, if r k = true then H k else 0) =
      ∑ k, H k := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases r k <;> simp

private theorem score_sum {ι : Type*} [Fintype ι]
    (A B : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    (witnessU * ((∑ k, A k) + (∑ k, B k)) +
      witnessV * ((∑ k, A k) - (∑ k, B k))).trace.re =
      ∑ k, (witnessU * (A k + B k) + witnessV * (A k - B k)).trace.re := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    Matrix.mul_sum, Matrix.mul_sum, ← Finset.sum_add_distrib, Matrix.trace_sum]
  exact Complex.re_sum _ _

private theorem trace_pair_sum {ι : Type*} [Fintype ι]
    (C : Matrix (Fin 2) (Fin 2) ℂ) (H : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    (C * ∑ k, H k).trace.re = ∑ k, (C * H k).trace.re := by
  rw [Matrix.mul_sum, Matrix.trace_sum]
  exact Complex.re_sum _ _

private theorem hidden_score_point (s t : Bool) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.PosSemidef) :
    (witnessU * ((if s then -M else M) + (if t then -M else M)) +
      witnessV * ((if s then -M else M) - (if t then -M else M))).trace.re ≤
      2 * (witnessC * M).trace.re := by
  have hp := RHLinalg.trace_mul_nonneg_of_posSemidef (witness_domination s t) hM
  change 0 ≤ ((witnessC - responseWitness s t) * M).trace.re at hp
  cases s <;> cases t <;>
    simp only [responseWitness, Bool.false_eq_true, Bool.true_eq_false,
      eq_self, ite_true, ite_false] at hp ⊢ <;>
    simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.mul_neg, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_neg,
      Complex.add_re, Complex.sub_re, Complex.neg_re] at hp ⊢ <;> linarith

private theorem lhs_bound (σ : Fin 2 → Bool → Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ 0 false + σ 0 true = marginalA) (h : HasLHS σ) :
    steeringScore σ ≤ 2 / 5 := by
  obtain ⟨H, hH, hmodel⟩ := h
  have hdiff (x : Fin 2) : σ x false - σ x true =
      ∑ k, if k x then -H k else H k :=
    (congrArg₂ (fun A B : Matrix (Fin 2) (Fin 2) ℂ => A - B)
      (hmodel x false).symm (hmodel x true).symm).trans
        (deterministic_difference H (fun k => k x))
  have htotal : (∑ k, H k) = marginalA :=
    (deterministic_total H (fun k => k 0)).symm.trans
      ((congrArg₂ (fun A B : Matrix (Fin 2) (Fin 2) ℂ => A + B)
        (hmodel 0 false) (hmodel 0 true)).trans hσ)
  let A : (Fin 2 → Bool) → Matrix (Fin 2) (Fin 2) ℂ :=
    fun k => if k 0 then -H k else H k
  let B : (Fin 2 → Bool) → Matrix (Fin 2) (Fin 2) ℂ :=
    fun k => if k 1 then -H k else H k
  have hscore : steeringScore σ =
      (witnessU * ((∑ k, A k) + (∑ k, B k)) +
        witnessV * ((∑ k, A k) - (∑ k, B k))).trace.re :=
    congrArg₂ (fun X Y : Matrix (Fin 2) (Fin 2) ℂ =>
      (witnessU * (X + Y) + witnessV * (X - Y)).trace.re) (hdiff 0) (hdiff 1)
  have hpoint : (∑ k, (witnessU * (A k + B k) + witnessV * (A k - B k)).trace.re) ≤
      ∑ k, 2 * (witnessC * H k).trace.re :=
    Finset.sum_le_sum fun k _ => hidden_score_point (k 0) (k 1) (H k) (hH k)
  have hsum : (∑ k, 2 * (witnessC * H k).trace.re) = 2 / 5 := by
    calc
      (∑ k, 2 * (witnessC * H k).trace.re) =
          2 * ∑ k, (witnessC * H k).trace.re := (Finset.mul_sum _ _ _).symm
      _ = 2 * (witnessC * ∑ k, H k).trace.re :=
        congrArg (fun x : ℝ => 2 * x) (trace_pair_sum witnessC H).symm
      _ = 2 * (witnessC * marginalA).trace.re :=
        congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => 2 * (witnessC * M).trace.re) htotal
      _ = 2 / 5 := by
        norm_num [witnessC, marginalA, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two, diagonal]
  exact (hscore.trans (score_sum A B)).le.trans (hpoint.trans_eq hsum)

private theorem state_steering : SteerableBA stateR := by
  refine ⟨2, measurements, measurements_projective, ?_⟩
  intro h
  have hm : assemblage stateR measurements 0 false +
      assemblage stateR measurements 0 true = marginalA := by
    rw [quantum_assemblage]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [quantumAssemblage, marginalA, diagonal]
  have hb := lhs_bound _ hm h
  have hq : steeringScore (assemblage stateR measurements) = 10197 / 25250 := by
    rw [quantum_assemblage]
    norm_num [steeringScore, quantumAssemblage, witnessU, witnessV,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hq] at hb
  norm_num at hb

/-- Spatial steering does not guarantee atemporality. -/
theorem result : ¬ claim := by
  intro h
  exact (h stateR state_density (Or.inl state_steering)).1 state_temporal

end D5.S3.Quantum.Contextuality.SteeringTemporalCompatibilityRefutation
