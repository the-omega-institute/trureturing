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
  · norm_num [Matrix.trace, Matrix.diag, stateR, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem state_temporal : TemporalForward stateR := by
  sorry

private theorem measurements_projective : BinaryProjective measurements := by
  constructor
  · intro x b
    constructor
    · change (measurements x b).conjTranspose = measurements x b
      simp only [measurements, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_one, pauli_hermitian]
      cases b <;> norm_num
    · fin_cases x <;> cases b <;>
        simp [measurements, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul, letter_mul, letterPhase, letterProduct,
          pauliMatrix.eq_1] <;> module
  · intro x
    ext i j
    simp [measurements, Matrix.add_apply, Matrix.smul_apply]
    ring

set_option maxHeartbeats 800000 in
private theorem lhs_bound (σ : Fin 2 → Bool → Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ 0 false + σ 0 true = marginalA) (h : HasLHS σ) :
    steeringScore σ ≤ 2 / 5 := by
  sorry

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
