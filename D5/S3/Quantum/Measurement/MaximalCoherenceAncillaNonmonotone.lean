/- GID: D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.claim; result=D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.result; claim=D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.claim
   digest: An identity ancilla increases maximal spectral-distance measurement coherence. -/

/-
result: proof_shape: bind-only.
escape_witness: none.
admission_basis: open-problem-resolution (#15378; Refuted).
Direct frozen dependencies (GID, declaration statement_id):
  D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled
    sha256:ef511c2d4d4f2b65619d661a40bc5115a91b08dc6dd3d34194d3d9b26b250c86
  D5/S3/Quantum/EnvironmentRecords.JointQubitEnvironmentMatrix
    sha256:178ee93563d50eb4c9e106c011782d3811ad43e12027d0db8658ad0760e36a12
  D5/S3/Quantum/FiniteDimensional.qubitX
    sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
  D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix
    sha256:ee496966fe099c646fb0f51761f3b1e446ac73f2e7b579da5586731706e8c52d
  D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard
    sha256:d28d3fee83d154e42cf2331eba2ffeb942edeed66e1ff8e9221f10b0b991ddc4
  D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2
    sha256:ef4ae1e2fc1bec9bf605d06598d58ce332db9ba1a90facd16a497c70ae0336f7
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker
    sha256:a0838f79000777eac14a35e86139cd9f264a8cd9569370843c5210242ee58673
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X
    sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z
    sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix
    sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
  D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM
    sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The identification C^2 tensor C^2 with Fin 4 is finProdFinEquiv: (i,j) maps to 2*i+j,
so coordinates are |00>, |01>, |10>, |11>. J is the reindexed Kronecker product X tensor I_2.
R is half the existing right partial trace in these coordinates.
All helper theorems are consumed bind-only adapters of pinned Mathlib facts and finite normalization.
  fallback_incoherent: proof_shape: bind-only; consumer(s): distances_nonempty, cmax_bddAbove; escape_witness: none.
  dInf_nonneg: proof_shape: bind-only; consumer(s): distances_bddBelow; escape_witness: none.
  distances_bddBelow: proof_shape: bind-only; consumer(s): coh_le; escape_witness: none.
  distances_nonempty: proof_shape: bind-only; consumer(s): coh_lower; escape_witness: none.
  coh_le: proof_shape: bind-only; consumer(s): cmax_bddAbove, sic_cmax_upper; escape_witness: none.
  coh_lower: proof_shape: bind-only; consumer(s): sic_ancilla_cmax_lower; escape_witness: none.
  norm_unitary_conj: proof_shape: bind-only; consumer(s): cmax_bddAbove, bell_effect_norm_lower; escape_witness: none.
  cmax_bddAbove: proof_shape: bind-only; consumer(s): coh_le_cmax; escape_witness: none.
  cmax_nonempty: proof_shape: bind-only; consumer(s): cmax_upper; escape_witness: none.
  coh_le_cmax: proof_shape: bind-only; consumer(s): sic_ancilla_cmax_lower; escape_witness: none.
  cmax_upper: proof_shape: bind-only; consumer(s): sic_cmax_upper; escape_witness: none.
  diag_incoherent: proof_shape: bind-only; consumer(s): sic_cmax_upper; escape_witness: none.
  conjugate_povm: proof_shape: bind-only; consumer(s): sic_cmax_upper; escape_witness: none.
  quadratic_le_norm: proof_shape: bind-only; consumer(s): expect_le_norm; escape_witness: none.
    owner: Mathlib ContinuousLinearMap.rayleighQuotient_le_norm; normalization: unit norm, real-inner symmetry, Matrix.l2_opNorm_toEuclideanCLM.
  J_kraus: proof_shape: bind-only; consumer(s): J_cp_unital; escape_witness: none.
  J_cp_unital: proof_shape: bind-only; consumer(s): result; escape_witness: none.
  s2_square: proof_shape: bind-only; consumer(s): bell_unitary, R_bell_diag; escape_witness: none.
  bell_table: proof_shape: bind-only; consumer(s): bell_unitary, R_bell_diag; escape_witness: none.
  bell_unitary: proof_shape: bind-only; consumer(s): bell_effect_norm_lower, sic_ancilla_cmax_lower; escape_witness: none.
  R_J: proof_shape: bind-only; consumer(s): bell_effect_norm_lower; escape_witness: none.
    owner: PartialTraceMutualInformation.partialTraceRight_kronecker; normalization: coordinate reindexing, trace of I_2, scalar factor.
  R_bell_diag: proof_shape: bind-only; consumer(s): bell_effect_norm_lower; escape_witness: none.
  tensorKet_norm: proof_shape: bind-only; consumer(s): partial_trace_expect_le_norm; escape_witness: none.
  expect_le_norm: proof_shape: bind-only; consumer(s): partial_trace_expect_le_norm; escape_witness: none.
  expect_partial_trace: proof_shape: bind-only; consumer(s): partial_trace_expect_le_norm; escape_witness: none.
  partial_trace_expect_le_norm: proof_shape: bind-only; consumer(s): bell_effect_norm_lower; escape_witness: none.
  R_sub: proof_shape: bind-only; consumer(s): bell_effect_norm_lower; escape_witness: none.
  R_neg: proof_shape: bind-only; consumer(s): bell_effect_norm_lower; escape_witness: none.
  expect_neg: proof_shape: bind-only; consumer(s): bell_effect_norm_lower; escape_witness: none.
  dot_self_eq_norm_sq: proof_shape: bind-only; consumer(s): expect_eigen, expect_shift; escape_witness: none.
    owner: Mathlib inner_self_eq_norm_sq_to_K; normalization: EuclideanSpace.inner_eq_star_dotProduct.
  expect_eigen: proof_shape: bind-only; consumer(s): bell_effect_norm_lower; escape_witness: none.
  expect_shift: proof_shape: bind-only; consumer(s): bell_effect_norm_lower; escape_witness: none.
  bell_effect_norm_lower: proof_shape: bind-only; consumer(s): sic_bell_distance_lower; escape_witness: none.
  s3_square: proof_shape: bind-only; consumer(s): sic_square, sic_offdiag_square_sum; escape_witness: none.
  sic_hermitian: proof_shape: bind-only; consumer(s): sic_square, sic_eigenvectors; escape_witness: none.
  sic_square: proof_shape: bind-only; consumer(s): sic_povm, sic_eigenvectors; escape_witness: none.
  sic_povm: proof_shape: bind-only; consumer(s): sic_cmax_upper, result; escape_witness: none.
  pauli_normSq: proof_shape: bind-only; consumer(s): sic_offdiag_square_sum; escape_witness: none.
  tetra_normSq: proof_shape: bind-only; consumer(s): sic_offdiag_square_sum; escape_witness: none.
  sic_offdiag_formula: proof_shape: bind-only; consumer(s): sic_offdiag_square_sum; escape_witness: none.
  sic_offdiag_square_sum: proof_shape: bind-only; consumer(s): sic_offdiag_sum_le; escape_witness: none.
  entry_le_norm: proof_shape: bind-only; consumer(s): hermitian_offdiag_norm; escape_witness: none.
  offdiag_norm_le: proof_shape: bind-only; consumer(s): hermitian_offdiag_norm; escape_witness: none.
  hermitian_offdiag_norm: proof_shape: bind-only; consumer(s): dephasing_distance; escape_witness: none.
  dephasing_distance: proof_shape: bind-only; consumer(s): sic_cmax_upper; escape_witness: none.
  unit_eigenvector_of_scaled_idempotent: proof_shape: bind-only; consumer(s): sic_eigenvectors; escape_witness: none.
  sic_trace: proof_shape: bind-only; consumer(s): sic_eigenvectors; escape_witness: none.
  sic_eigenvectors: proof_shape: bind-only; consumer(s): sic_bell_distance_lower; escape_witness: none.
  sic_offdiag_sum_le: proof_shape: bind-only; consumer(s): sic_cmax_upper; escape_witness: none.
  sic_cmax_upper: proof_shape: bind-only; consumer(s): result; escape_witness: none.
  upper_strict: proof_shape: bind-only; consumer(s): result; escape_witness: none.
  sic_bell_distance_lower: proof_shape: bind-only; consumer(s): sic_ancilla_cmax_lower; escape_witness: none.
  sic_ancilla_cmax_lower: proof_shape: bind-only; consumer(s): result; escape_witness: none.
Per-declaration Direct frozen dependencies (identities are given in the registry above):
  IsIncoherent: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  dInf: none.
  coh: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  cmax: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  IsCPUnitalDual: none.
  claim: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  fallback_incoherent: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  dInf_nonneg: none.
  distances_bddBelow: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  distances_nonempty: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  coh_le: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  coh_lower: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  norm_unitary_conj: none.
  cmax_bddAbove: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  cmax_nonempty: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  coh_le_cmax: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  cmax_upper: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  diag_incoherent: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  conjugate_povm: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  quadratic_le_norm: none.
  K: none.
  J: none.
  J_kraus: none.
  J_cp_unital: none.
  s2_square: none.
  U_B: D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled, D5/S3/Quantum/EnvironmentRecords.JointQubitEnvironmentMatrix, D5/S3/Quantum/FiniteDimensional.qubitX, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard.
  bell_table: D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled, D5/S3/Quantum/EnvironmentRecords.JointQubitEnvironmentMatrix, D5/S3/Quantum/FiniteDimensional.qubitX, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.
  bell_unitary: D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled, D5/S3/Quantum/EnvironmentRecords.JointQubitEnvironmentMatrix, D5/S3/Quantum/FiniteDimensional.qubitX, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.
  R: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight.
  R_J: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight, D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker.
  R_bell_diag: D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled, D5/S3/Quantum/EnvironmentRecords.JointQubitEnvironmentMatrix, D5/S3/Quantum/FiniteDimensional.qubitX, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2, D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.
  expect: none.
  tensorKet: none.
  tensorKet_norm: none.
  expect_le_norm: none.
  expect_partial_trace: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight.
  partial_trace_expect_le_norm: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight.
  R_sub: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight.
  R_neg: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight.
  expect_neg: none.
  dot_self_eq_norm_sq: none.
  expect_eigen: none.
  expect_shift: none.
  bell_effect_norm_lower: D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled, D5/S3/Quantum/EnvironmentRecords.JointQubitEnvironmentMatrix, D5/S3/Quantum/FiniteDimensional.qubitX, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2, D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight, D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.
  signs: none.
  M_SIC: D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix.
  s3_square: none.
  sic_hermitian: D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix.
  sic_square: D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix.
  sic_povm: D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix.
  pauli_normSq: none.
  tetra_normSq: none.
  sic_offdiag_formula: D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix.
  sic_offdiag_square_sum: D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix.
  entry_le_norm: none.
  offdiag_norm_le: none.
  hermitian_offdiag_norm: none.
  dephasing_distance: none.
  unit_eigenvector_of_scaled_idempotent: none.
  sic_trace: D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix.
  sic_eigenvectors: D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix.
  sic_offdiag_sum_le: D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix.
  sic_cmax_upper: D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix, D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  upper_strict: none.
  sic_bell_distance_lower: D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled, D5/S3/Quantum/EnvironmentRecords.JointQubitEnvironmentMatrix, D5/S3/Quantum/FiniteDimensional.qubitX, D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2, D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight, D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix, D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  sic_ancilla_cmax_lower: D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled, D5/S3/Quantum/EnvironmentRecords.JointQubitEnvironmentMatrix, D5/S3/Quantum/FiniteDimensional.qubitX, D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2, D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight, D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix, D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
  result: D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled, D5/S3/Quantum/EnvironmentRecords.JointQubitEnvironmentMatrix, D5/S3/Quantum/FiniteDimensional.qubitX, D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard, D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2, D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight, D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z, D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix, D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
-/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
import D5.S3.Quantum.Dynamics.PositivePauliClockOrder

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (blochMatrix)

namespace D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone


def IsIncoherent {n d : Nat} (B : Fin n → (Matrix (Fin d) (Fin d) Complex)) : Prop :=
  IsPOVM B ∧ ∀ x, (B x).IsDiag

def dInf {n d : Nat} (A B : Fin n → (Matrix (Fin d) (Fin d) Complex)) : Real :=
  (1 / 2) * ∑ x, ‖A x - B x‖

def coh {n d : Nat} (A : Fin n → (Matrix (Fin d) (Fin d) Complex)) : Real :=
  sInf {r | ∃ B, IsIncoherent B ∧ r = dInf A B}

def cmax {n d : Nat} (A : Fin n → (Matrix (Fin d) (Fin d) Complex)) : Real :=
  sSup {r | ∃ U ∈ Matrix.unitaryGroup (Fin d) Complex,
    r = coh (fun x => star U * A x * U)}

def IsCPUnitalDual {d e : Nat} (Phi : (Matrix (Fin d) (Fin d) Complex) → (Matrix (Fin e) (Fin e) Complex)) : Prop :=
  ∃ (k : Nat) (K : Fin k → Matrix (Fin d) (Fin e) Complex),
    ∑ j, (K j)ᴴ * K j = 1 ∧ ∀ X, Phi X = ∑ j, (K j)ᴴ * X * K j

def claim : Prop :=
  ∀ (d e n : Nat) (A : Fin n → (Matrix (Fin d) (Fin d) Complex)) (Phi : (Matrix (Fin d) (Fin d) Complex) → (Matrix (Fin e) (Fin e) Complex))
    (alpha : Real) (q : Fin n → Real),
    2 < n → IsPOVM A → IsCPUnitalDual Phi → 0 ≤ alpha → alpha ≤ 1 →
    (∀ x, 0 ≤ q x) → ∑ x, q x = 1 →
    cmax (fun x => (alpha : Complex) • Phi (A x) +
      (((1 - alpha) * q x : Real) : Complex) • (1 : (Matrix (Fin e) (Fin e) Complex))) ≤ cmax A


private lemma fallback_incoherent {d : Nat} : IsIncoherent ((Pi.single (0 : Fin 4) (1 : Matrix (Fin d) (Fin d) Complex) : Fin 4 → Matrix (Fin d) (Fin d) Complex)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x
    by_cases h : x = 0
    · simpa [Pi.single_apply, h] using (Matrix.PosSemidef.one : (1 : (Matrix (Fin d) (Fin d) Complex)).PosSemidef)
    · simpa [Pi.single_apply, h] using (Matrix.PosSemidef.zero : (0 : (Matrix (Fin d) (Fin d) Complex)).PosSemidef)
  · simp [Pi.single_apply, Fin.sum_univ_succ]
  · intro x
    by_cases h : x = 0
    · simpa [Pi.single_apply, h] using (Matrix.isDiag_one : (1 : (Matrix (Fin d) (Fin d) Complex)).IsDiag)
    · simpa [Pi.single_apply, h] using (Matrix.isDiag_zero : (0 : (Matrix (Fin d) (Fin d) Complex)).IsDiag)

private lemma dInf_nonneg {d n : Nat} (A B : Fin n → (Matrix (Fin d) (Fin d) Complex)) : 0 ≤ dInf A B := by
  unfold dInf
  positivity

private lemma distances_bddBelow {d n : Nat} (A : Fin n → (Matrix (Fin d) (Fin d) Complex)) :
    BddBelow {r | ∃ B, IsIncoherent B ∧ r = dInf A B} := by
  refine ⟨0, ?_⟩
  rintro r ⟨B, hB, rfl⟩
  exact dInf_nonneg A B

private lemma distances_nonempty {d : Nat} (A : Fin 4 → (Matrix (Fin d) (Fin d) Complex)) :
    {r | ∃ B, IsIncoherent B ∧ r = dInf A B}.Nonempty := by
  exact ⟨dInf A (Pi.single (0 : Fin 4) 1), (Pi.single (0 : Fin 4) 1), fallback_incoherent, rfl⟩

private lemma coh_le {d n : Nat} (A B : Fin n → (Matrix (Fin d) (Fin d) Complex)) (hB : IsIncoherent B) :
    coh A ≤ dInf A B := by
  exact csInf_le (distances_bddBelow A) ⟨B, hB, rfl⟩

private lemma coh_lower {d : Nat} (A : Fin 4 → (Matrix (Fin d) (Fin d) Complex)) (c : Real)
    (h : ∀ B, IsIncoherent B → c ≤ dInf A B) : c ≤ coh A := by
  apply le_csInf (distances_nonempty A)
  rintro r ⟨B, hB, rfl⟩
  exact h B hB

private lemma norm_unitary_conj {d : Nat} (X U : (Matrix (Fin d) (Fin d) Complex))
    (hU : U ∈ Matrix.unitaryGroup (Fin d) Complex) :
    ‖star U * X * U‖ = ‖X‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ hU]
  exact CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hU)

private lemma cmax_bddAbove {d : Nat} (A : Fin 4 → (Matrix (Fin d) (Fin d) Complex)) :
    BddAbove {r | ∃ U ∈ Matrix.unitaryGroup (Fin d) Complex,
      r = coh (fun x => star U * A x * U)} := by
  refine ⟨(1/2) * ∑ x : Fin 4, (‖A x‖ + ‖(Pi.single (0 : Fin 4) (1 : Matrix (Fin d) (Fin d) Complex) : Fin 4 → Matrix (Fin d) (Fin d) Complex) x‖), ?_⟩
  rintro r ⟨U, hU, rfl⟩
  refine (coh_le _ (Pi.single (0 : Fin 4) 1) fallback_incoherent).trans ?_
  unfold dInf
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro x hx
  have h := norm_sub_le (star U * A x * U) ((Pi.single (0 : Fin 4) (1 : Matrix (Fin d) (Fin d) Complex) : Fin 4 → Matrix (Fin d) (Fin d) Complex) x)
  simpa only [norm_unitary_conj (A x) U hU] using h

private lemma cmax_nonempty {d n : Nat} (A : Fin n → (Matrix (Fin d) (Fin d) Complex)) :
    {r | ∃ U ∈ Matrix.unitaryGroup (Fin d) Complex,
      r = coh (fun x => star U * A x * U)}.Nonempty := by
  refine ⟨coh A, 1, ?_, ?_⟩
  · exact Submonoid.one_mem _
  · simp

private lemma coh_le_cmax {d : Nat} (A : Fin 4 → (Matrix (Fin d) (Fin d) Complex)) (U : (Matrix (Fin d) (Fin d) Complex))
    (hU : U ∈ Matrix.unitaryGroup (Fin d) Complex) :
    coh (fun x => star U * A x * U) ≤ cmax A := by
  exact le_csSup (cmax_bddAbove A) ⟨U, hU, rfl⟩

private lemma cmax_upper {d n : Nat} (A : Fin n → (Matrix (Fin d) (Fin d) Complex)) (c : Real)
    (h : ∀ U ∈ Matrix.unitaryGroup (Fin d) Complex,
      coh (fun x => star U * A x * U) ≤ c) : cmax A ≤ c := by
  apply csSup_le (cmax_nonempty A)
  rintro r ⟨U, hU, rfl⟩
  exact h U hU

private lemma diag_incoherent {d n : Nat} (A : Fin n → (Matrix (Fin d) (Fin d) Complex)) (hA : IsPOVM A) :
    IsIncoherent (fun x => Matrix.diagonal (fun j => A x j j)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x
    exact Matrix.PosSemidef.diagonal (fun j => (hA.1 x).diag_nonneg)
  · ext i j
    by_cases h : i = j
    · subst j
      simpa [Matrix.sum_apply] using congrArg (fun X : (Matrix (Fin d) (Fin d) Complex) => X i i) hA.2
    · simp [Matrix.sum_apply, Matrix.diagonal_apply, h, Matrix.one_apply]
  · intro x
    exact Matrix.isDiag_diagonal _

private lemma conjugate_povm {d n : Nat} (A : Fin n → (Matrix (Fin d) (Fin d) Complex)) (hA : IsPOVM A)
    (U : (Matrix (Fin d) (Fin d) Complex)) (hU : U ∈ Matrix.unitaryGroup (Fin d) Complex) :
    IsPOVM (fun x => star U * A x * U) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact (hA.1 x).conjTranspose_mul_mul_same U
  · rw [← Matrix.sum_mul, ← Matrix.mul_sum, hA.2, mul_one]
    exact Matrix.mem_unitaryGroup_iff'.mp hU

private lemma quadratic_le_norm {d : Nat} (Y : (Matrix (Fin d) (Fin d) Complex))
    (v : EuclideanSpace Complex (Fin d)) (hv : ‖v‖ = 1) :
    (inner Complex v (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := Complex) Y v)).re ≤ ‖Y‖ := by
  have h := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := Complex) Y).rayleighQuotient_le_norm v
  have h' : |(inner Complex v (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := Complex) Y v)).re| ≤ ‖Y‖ := by
    simpa [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, hv, inner_re_symm,
      Matrix.l2_opNorm_toEuclideanCLM] using h
  exact (le_abs_self _).trans h'

-- Fin 4 is ordered as |00>, |01>, |10>, |11>.
private def K (j : Fin 2) : Matrix (Fin 2) (Fin 4) Complex :=
  (1 : Matrix (Fin 4) (Fin 4) Complex).submatrix
    (fun i => finProdFinEquiv (i, j)) id

private def J (X : Matrix (Fin 2) (Fin 2) Complex) : Matrix (Fin 4) (Fin 4) Complex :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kronecker X (1 : Matrix (Fin 2) (Fin 2) Complex))

private lemma J_kraus (X : (Matrix (Fin 2) (Fin 2) Complex)) : J X = ∑ j, (K j)ᴴ * X * K j := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [J, Matrix.reindex, Matrix.kronecker, Matrix.kroneckerMap, Matrix.submatrix, Matrix.one_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, K, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Fin.sum_univ_succ]

private lemma J_cp_unital : IsCPUnitalDual J := by
  refine ⟨2, K, ?_, J_kraus⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [K, Matrix.submatrix, Matrix.one_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Fin.sum_univ_succ]

private lemma s2_square : ((Real.sqrt 2)⁻¹) ^ 2 = 1/2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0:Real) ≤ 2)]
  norm_num

private def U_B : Matrix (Fin 4) (Fin 4) Complex :=
  (Matrix.reindex finProdFinEquiv finProdFinEquiv
    (D5.S3.Quantum.Dynamics.PositivePauliClockOrder.controlled
      (1 : Matrix (Fin 2) (Fin 2) Complex) D5.S3.Quantum.FiniteDimensional.qubitX *
      Matrix.kronecker D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard
        (1 : Matrix (Fin 2) (Fin 2) Complex))).submatrix id (Equiv.swap 1 2)

private lemma bell_table : U_B = (((Real.sqrt 2)⁻¹) : Complex) •
    !![1,1,0,0;0,0,1,1;0,0,1,-1;1,-1,0,0] := by
  have hs : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [inv_eq_one_div]
    apply (eq_div_iff (ne_of_gt hp)).2
    nlinarith [Real.sq_sqrt (by norm_num : (0:Real) ≤ 2)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U_B, D5.S3.Quantum.Dynamics.PositivePauliClockOrder.controlled, Equiv.swap_apply_def, Matrix.one_apply, Matrix.reindex, Matrix.submatrix, Matrix.blockDiagonal,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, finProdFinEquiv, Fin.divNat, Fin.modNat,
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard,
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ, hs]

private lemma bell_unitary : U_B ∈ Matrix.unitaryGroup (Fin 4) Complex := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  have hs : (((Real.sqrt 2)⁻¹) : Complex)^2 = 1/2 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, s2_square]
    norm_num
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [bell_table, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> try simp [hs]

-- The normalized partial trace, in Kraus-compression form.
private def R (Y : Matrix (Fin 4) (Fin 4) Complex) : Matrix (Fin 2) (Fin 2) Complex :=
  (1/2 : Complex) • partialTraceRight
    (Y.submatrix (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) finProdFinEquiv)

private lemma R_J (X : (Matrix (Fin 2) (Fin 2) Complex)) : R (J X) = X := by
  unfold R J
  simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id]
  rw [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_kronecker,
    Matrix.trace_one, smul_smul]
  norm_num

private lemma R_bell_diag (B : (Matrix (Fin 4) (Fin 4) Complex)) (hB : B.IsDiag) :
    R (U_B * B * star U_B) = (B.trace/4) • (1 : (Matrix (Fin 2) (Fin 2) Complex)) := by
  rw [← hB.diagonal_diag]
  have hs : (((Real.sqrt 2)⁻¹) : Complex)^2 = 1/2 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, s2_square]
    norm_num
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [R, partialTraceRight, Matrix.submatrix, finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.one_apply, bell_table, K, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.trace, Fin.sum_univ_two, Fin.sum_univ_succ] <;>
    ring_nf <;> try simp [hs] <;> ring

private def expect {d : Nat} (Y : (Matrix (Fin d) (Fin d) Complex)) (psi : Fin d → Complex) : Real :=
  (star psi ⬝ᵥ (Y *ᵥ psi)).re

private def tensorKet (psi : Fin 2 → Complex) (j : Fin 2) : Fin 4 → Complex :=
  (K j)ᴴ *ᵥ psi

private lemma tensorKet_norm (psi : Fin 2 → Complex) (j : Fin 2) :
    ‖WithLp.toLp 2 (tensorKet psi j)‖ = ‖WithLp.toLp 2 psi‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  fin_cases j <;>
    simp [EuclideanSpace.norm_sq_eq, tensorKet, K, Matrix.mulVec, dotProduct, Matrix.submatrix, Matrix.one_apply, Matrix.conjTranspose_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_succ]

private lemma expect_le_norm {d : Nat} (Y : (Matrix (Fin d) (Fin d) Complex)) (psi : Fin d → Complex)
    (hpsi : ‖WithLp.toLp 2 psi‖ = 1) : expect Y psi ≤ ‖Y‖ := by
  have h := quadratic_le_norm Y (WithLp.toLp 2 psi) hpsi
  simpa [expect, Matrix.toEuclideanCLM_toLp, PiLp.inner_apply,
    RCLike.inner_apply, dotProduct, mul_comm] using h

private lemma expect_partial_trace (Y : (Matrix (Fin 4) (Fin 4) Complex)) (psi : Fin 2 → Complex) :
    expect (R Y) psi = (1/2) * ∑ j, expect Y (tensorKet psi j) := by
  simp [expect, R, partialTraceRight, K, tensorKet, Matrix.submatrix, Matrix.one_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec,
    dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im]
  ring

private lemma partial_trace_expect_le_norm (Y : (Matrix (Fin 4) (Fin 4) Complex)) (psi : Fin 2 → Complex)
    (hpsi : ‖WithLp.toLp 2 psi‖ = 1) : expect (R Y) psi ≤ ‖Y‖ := by
  rw [expect_partial_trace]
  have h (j : Fin 2) : expect Y (tensorKet psi j) ≤ ‖Y‖ :=
    expect_le_norm Y _ (by rw [tensorKet_norm, hpsi])
  simp only [Fin.sum_univ_two]
  linarith [h 0, h 1]

private lemma R_sub (X Y : (Matrix (Fin 4) (Fin 4) Complex)) : R (X-Y) = R X - R Y := by
  ext i j
  simp [R, partialTraceRight, Matrix.submatrix, Finset.sum_sub_distrib, mul_sub]

private lemma R_neg (Y : (Matrix (Fin 4) (Fin 4) Complex)) : R (-Y) = -(R Y) := by
  ext i j
  simp [R, partialTraceRight, Matrix.submatrix]
  ring

private lemma expect_neg {d : Nat} (Y : (Matrix (Fin d) (Fin d) Complex)) (psi : Fin d → Complex) :
    expect (-Y) psi = - expect Y psi := by
  simp [expect, Matrix.neg_mulVec]

private lemma dot_self_eq_norm_sq {d : Nat} (psi : Fin d → Complex) :
    star psi ⬝ᵥ psi = (‖WithLp.toLp 2 psi‖ : Complex)^2 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using!
    (inner_self_eq_norm_sq_to_K (𝕜 := Complex)
      (E := EuclideanSpace Complex (Fin d)) (WithLp.toLp 2 psi))

private lemma expect_eigen {d : Nat} (A : (Matrix (Fin d) (Fin d) Complex)) (psi : Fin d → Complex) (lam : Real)
    (hpsi : ‖WithLp.toLp 2 psi‖ = 1) (he : A *ᵥ psi = (lam : Complex) • psi) :
    expect A psi = lam := by
  unfold expect
  rw [he, dotProduct_smul]
  have h := dot_self_eq_norm_sq psi
  rw [h, hpsi]
  simp

private lemma expect_shift {d : Nat} (A : (Matrix (Fin d) (Fin d) Complex)) (psi : Fin d → Complex) (q : Complex)
    (hpsi : ‖WithLp.toLp 2 psi‖ = 1) :
    expect (A-q • (1:(Matrix (Fin d) (Fin d) Complex))) psi = expect A psi - q.re := by
  have h : (star psi ⬝ᵥ psi) = (1 : Complex) := by
    rw [dot_self_eq_norm_sq, hpsi]
    norm_num
  simp [expect, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, h]

private lemma bell_effect_norm_lower (A : (Matrix (Fin 2) (Fin 2) Complex)) (B : (Matrix (Fin 4) (Fin 4) Complex)) (hB : B.IsDiag)
    (lo hi : Real) (v w : Fin 2 → Complex)
    (hv : ‖WithLp.toLp 2 v‖ = 1) (hw : ‖WithLp.toLp 2 w‖ = 1)
    (hvA : A *ᵥ v = (hi : Complex) • v)
    (hwA : A *ᵥ w = (lo : Complex) • w) :
    (hi-lo)/2 ≤ ‖star U_B * J A * U_B - B‖ := by
  let Y := J A - U_B * B * star U_B
  have hRY : R Y = A - (B.trace/4) • (1:(Matrix (Fin 2) (Fin 2) Complex)) := by
    dsimp only [Y]
    rw [R_sub, R_J, R_bell_diag B hB]
  have hplus := partial_trace_expect_le_norm Y v hv
  rw [hRY, expect_shift _ _ _ hv, expect_eigen _ _ _ hv hvA] at hplus
  have hminus := partial_trace_expect_le_norm (-Y) w hw
  rw [R_neg, expect_neg, hRY, expect_shift _ _ _ hw,
    expect_eigen _ _ _ hw hwA, norm_neg] at hminus
  have hnorm : ‖Y‖ = ‖star U_B * J A * U_B - B‖ := by
    have he : star U_B * Y * U_B = star U_B * J A * U_B - B := by
      dsimp [Y]
      rw [Matrix.mul_sub, Matrix.sub_mul]
      congr 1
      calc
        star U_B * (U_B * B * star U_B) * U_B =
            (star U_B * U_B) * B * (star U_B * U_B) := by noncomm_ring
        _ = B := by rw [Matrix.mem_unitaryGroup_iff'.mp bell_unitary]; simp
    rw [← norm_unitary_conj Y U_B bell_unitary, he]
  rw [hnorm] at hplus hminus
  linarith


private def signs : Fin 4 → Fin 3 → Real := ![![1,1,1], ![1,-1,-1], ![-1,1,-1], ![-1,-1,1]]

private def M_SIC (x : Fin 4) : Matrix (Fin 2) (Fin 2) Complex :=
  (1/2 : Complex) • blochMatrix 1
    (WithLp.toLp 2 (fun i => signs x i * (Real.sqrt 3)⁻¹))

private lemma s3_square : ((Real.sqrt 3)⁻¹) ^ 2 = 1/3 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0:Real) ≤ 3)]
  norm_num

private lemma sic_hermitian (x : Fin 4) : (M_SIC x)ᴴ = M_SIC x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M_SIC, blochMatrix, Matrix.conjTranspose_apply, map_sub, map_add, map_mul] <;> ring

private lemma sic_square (x : Fin 4) : (M_SIC x)ᴴ * M_SIC x = (1/2:Complex) • M_SIC x := by
  rw [sic_hermitian]
  have hs : (((Real.sqrt 3)⁻¹) : Complex) ^ 2 = 1/3 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, s3_square]
    norm_num
  ext i j
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    simp [M_SIC, blochMatrix, signs, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] <;>
    ring_nf <;> simp [Complex.I_sq, hs] <;> ring

private lemma sic_povm : IsPOVM M_SIC := by
  refine ⟨?_, ?_⟩
  · intro x
    have h := (Matrix.posSemidef_conjTranspose_mul_self (M_SIC x)).smul
      (show (0:Complex) ≤ 2 by norm_num)
    rw [sic_square, smul_smul] at h
    norm_num at h
    exact h
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M_SIC, blochMatrix, signs, Fin.sum_univ_succ,
        Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] <;> ring

private lemma pauli_normSq (a b : Fin 2 → Complex) :
    Complex.normSq (star (a 0)*b 1 + star (a 1)*b 0) +
    Complex.normSq (-Complex.I*star (a 0)*b 1 + Complex.I*star (a 1)*b 0) +
    Complex.normSq (star (a 0)*b 0 - star (a 1)*b 1) =
    2*(Complex.normSq (a 0)+Complex.normSq (a 1))*
      (Complex.normSq (b 0)+Complex.normSq (b 1)) -
      Complex.normSq (star (a 0)*b 0 + star (a 1)*b 1) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

private lemma tetra_normSq (h x y z : Complex) (s : Real) :
    ∑ i : Fin 4, Complex.normSq ((h + (s : Complex)*
      ((signs i 0 : Complex)*x + (signs i 1 : Complex)*y + (signs i 2 : Complex)*z))/4) =
    (Complex.normSq h + s^2*(Complex.normSq x + Complex.normSq y + Complex.normSq z))/4 := by
  simp [Fin.sum_univ_succ, signs, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

private lemma sic_offdiag_formula (U : (Matrix (Fin 2) (Fin 2) Complex)) (i : Fin 4) :
    (star U * M_SIC i * U) 0 1 =
    ((star (U 0 0)*U 0 1 + star (U 1 0)*U 1 1) + (((Real.sqrt 3)⁻¹) : Complex)*
      ((signs i 0 : Complex)*(star (U 0 0)*U 1 1 + star (U 1 0)*U 0 1) +
       (signs i 1 : Complex)*(-Complex.I*star (U 0 0)*U 1 1 + Complex.I*star (U 1 0)*U 0 1) +
       (signs i 2 : Complex)*(star (U 0 0)*U 0 1 - star (U 1 0)*U 1 1)))/4 := by
  simp [M_SIC, blochMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

private lemma sic_offdiag_square_sum (U : (Matrix (Fin 2) (Fin 2) Complex))
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) Complex) :
    ∑ i, ‖(star U * M_SIC i * U) 0 1‖^2 = 1/6 := by
  have hu := Matrix.mem_unitaryGroup_iff'.mp hU
  have h0 : Complex.normSq (U 0 0)+Complex.normSq (U 1 0) = 1 := by
    have h := congrArg (fun X : (Matrix (Fin 2) (Fin 2) Complex) => (X 0 0).re) hu
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.mul_re, Complex.normSq_apply] using h
  have h1 : Complex.normSq (U 0 1)+Complex.normSq (U 1 1) = 1 := by
    have h := congrArg (fun X : (Matrix (Fin 2) (Fin 2) Complex) => (X 1 1).re) hu
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.mul_re, Complex.normSq_apply] using h
  have h01 : star (U 0 0)*U 0 1 + star (U 1 0)*U 1 1 = 0 := by
    have h := congrArg (fun X : (Matrix (Fin 2) (Fin 2) Complex) => X 0 1) hu
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Fin.sum_univ_two] using h
  simp_rw [Complex.sq_norm, sic_offdiag_formula]
  rw [← Complex.ofReal_inv, tetra_normSq]
  have hp :
      Complex.normSq (star (U 0 0)*U 1 1 + star (U 1 0)*U 0 1) +
      Complex.normSq (-Complex.I*star (U 0 0)*U 1 1 + Complex.I*star (U 1 0)*U 0 1) +
      Complex.normSq (star (U 0 0)*U 0 1 - star (U 1 0)*U 1 1) = 2 := by
    have hp' :
        Complex.normSq (star (U 0 0)*U 1 1 + star (U 1 0)*U 0 1) +
        Complex.normSq (-Complex.I*star (U 0 0)*U 1 1 + Complex.I*star (U 1 0)*U 0 1) +
        Complex.normSq (star (U 0 0)*U 0 1 - star (U 1 0)*U 1 1) =
        2*(Complex.normSq (U 0 0)+Complex.normSq (U 1 0))*
          (Complex.normSq (U 0 1)+Complex.normSq (U 1 1)) -
          Complex.normSq (star (U 0 0)*U 0 1 + star (U 1 0)*U 1 1) :=
      pauli_normSq (fun j => U j 0) (fun j => U j 1)
    simpa only [h0, h1, h01, Complex.normSq_zero, mul_one, sub_zero] using hp'
  rw [h01, hp, s3_square]
  norm_num

private lemma entry_le_norm {d : Nat} (A : (Matrix (Fin d) (Fin d) Complex)) (i j : Fin d) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace Complex (Fin d) := PiLp.single 2 j 1
  calc
    ‖A i j‖ = ‖((EuclideanSpace.equiv (Fin d) Complex).symm (A *ᵥ e)) i‖ := by
      simp [e, Matrix.mulVec]
    _ ≤ ‖(EuclideanSpace.equiv (Fin d) Complex).symm (A *ᵥ e)‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖A‖ * ‖e‖ := A.l2_opNorm_mulVec e
    _ = ‖A‖ := by simp [e]

private lemma offdiag_norm_le (a b : Complex) : ‖(!![0,a;b,0] : (Matrix (Fin 2) (Fin 2) Complex))‖ ≤ max ‖a‖ ‖b‖ := by
  let M : (Matrix (Fin 2) (Fin 2) Complex) := !![0,a;b,0]
  have hprod : Mᴴ * M = Matrix.diagonal ![(Complex.normSq b : Complex), (Complex.normSq a : Complex)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Complex.normSq_eq_conj_mul_self]
  have hn : ‖M‖ ^ 2 = ‖Mᴴ * M‖ := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]; ring
  have hb : ‖Mᴴ * M‖ ≤ (max ‖a‖ ‖b‖)^2 := by
    rw [hprod, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).mpr
    intro i
    fin_cases i
    · simpa [Complex.normSq_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖b‖)] using
        (pow_le_pow_left₀ (norm_nonneg b) (le_max_right ‖a‖ ‖b‖) 2)
    · simpa [Complex.normSq_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖a‖)] using
        (pow_le_pow_left₀ (norm_nonneg a) (le_max_left ‖a‖ ‖b‖) 2)
  have hm : 0 ≤ max ‖a‖ ‖b‖ := le_trans (norm_nonneg a) (le_max_left _ _)
  have := norm_nonneg M
  change ‖M‖ ≤ max ‖a‖ ‖b‖
  nlinarith

private lemma hermitian_offdiag_norm (a : Complex) : ‖(!![0,a;star a,0] : (Matrix (Fin 2) (Fin 2) Complex))‖ = ‖a‖ := by
  refine le_antisymm ?_ ?_
  · simpa using offdiag_norm_le a (star a)
  · simpa using entry_le_norm (!![0,a;star a,0] : (Matrix (Fin 2) (Fin 2) Complex)) 0 1

private lemma dephasing_distance {n : Nat} (A : Fin n → (Matrix (Fin 2) (Fin 2) Complex))
    (hA : ∀ x, (A x).IsHermitian) :
    dInf A (fun x => Matrix.diagonal (fun j => A x j j)) = (1/2) * ∑ x, ‖A x 0 1‖ := by
  unfold dInf
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hh : A x 1 0 = star (A x 0 1) := by
    have h := congrArg (fun X : (Matrix (Fin 2) (Fin 2) Complex) => X 1 0) (hA x)
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using h.symm
  have he : A x - Matrix.diagonal (fun j => A x j j) = !![0,A x 0 1;star (A x 0 1),0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hh]
  rw [he, hermitian_offdiag_norm]

private lemma unit_eigenvector_of_scaled_idempotent {d : Nat} (A : (Matrix (Fin d) (Fin d) Complex)) (t : Complex)
    (hA : A ≠ 0) (hAA : A*A = t • A) :
    ∃ v : EuclideanSpace Complex (Fin d), ‖v‖ = 1 ∧
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := Complex) A v = t • v := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := Complex) A
  have hT : T ≠ 0 := by
    intro h
    apply hA
    apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := Complex)).injective
    simpa [T] using h
  have hex : ∃ w, T w ≠ 0 := by
    by_contra! h
    exact hT (by apply ContinuousLinearMap.ext; intro w; exact h w)
  obtain ⟨w, hw⟩ := hex
  have hTT : T*T = t • T := by
    dsimp [T]
    rw [← map_mul, hAA, map_smul]
  have he : T (T w) = t • T w := by
    have h := congrArg (fun F : EuclideanSpace Complex (Fin d) →L[Complex]
      EuclideanSpace Complex (Fin d) => F w) hTT
    simpa using h
  have hn : ‖T w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  refine ⟨((‖T w‖⁻¹ : Real) : Complex) • T w, ?_, ?_⟩
  · rw [norm_smul]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hn]
  · rw [map_smul, he, smul_comm]

private lemma sic_trace (x : Fin 4) : (M_SIC x).trace = 1/2 := by
  simp [Matrix.trace, M_SIC, blochMatrix, Fin.sum_univ_two,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub]
  ring

private lemma sic_eigenvectors (x : Fin 4) :
    ∃ v w : Fin 2 → Complex,
      ‖WithLp.toLp 2 v‖ = 1 ∧ ‖WithLp.toLp 2 w‖ = 1 ∧
      M_SIC x *ᵥ v = (1/2:Complex) • v ∧ M_SIC x *ᵥ w = 0 := by
  have hA : M_SIC x ≠ 0 := by
    intro h
    have h' := sic_trace x
    rw [h] at h'
    norm_num at h'
  have hAA : M_SIC x * M_SIC x = (1/2:Complex) • M_SIC x := by
    simpa [sic_hermitian] using sic_square x
  let P : (Matrix (Fin 2) (Fin 2) Complex) := (1/2:Complex) • 1 - M_SIC x
  have hP : P ≠ 0 := by
    intro h
    have ht : P.trace = 1/2 := by
      norm_num [P, Matrix.trace_sub, Matrix.trace_smul, sic_trace]
    rw [h] at ht
    norm_num at ht
  have hPP : P*P = (1/2:Complex) • P := by
    dsimp [P]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, one_mul, mul_one, hAA, smul_sub]
    module
  obtain ⟨v, hv, he⟩ := unit_eigenvector_of_scaled_idempotent (M_SIC x) (1/2) hA hAA
  obtain ⟨w, hw, hwP⟩ := unit_eigenvector_of_scaled_idempotent P (1/2) hP hPP
  refine ⟨WithLp.ofLp v, WithLp.ofLp w, ?_, ?_, ?_, ?_⟩
  · simpa using hv
  · simpa using hw
  · have h := congrArg WithLp.ofLp he
    simpa [Matrix.ofLp_toEuclideanCLM] using h
  · have h := congrArg WithLp.ofLp hwP
    have hz : (1/2:Complex) • WithLp.ofLp w - M_SIC x *ᵥ WithLp.ofLp w =
        (1/2:Complex) • WithLp.ofLp w := by
      simpa [P, Matrix.ofLp_toEuclideanCLM, Matrix.sub_mulVec, Matrix.smul_mulVec] using h
    exact (sub_eq_self.mp hz)

private lemma sic_offdiag_sum_le (U : (Matrix (Fin 2) (Fin 2) Complex))
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) Complex) :
    ∑ i, ‖(star U * M_SIC i * U) 0 1‖ ≤ Real.sqrt (2/3) := by
  let f := fun i : Fin 4 => ‖(star U * M_SIC i * U) 0 1‖
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4)) f (fun _ => (1:Real))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  have he : ∑ i, f i^2 = 1/6 := sic_offdiag_square_sum U hU
  rw [he] at hcs
  have hs := Real.sq_sqrt (by norm_num : (0:Real) ≤ 2/3)
  have hnonneg : 0 ≤ ∑ i, f i := Finset.sum_nonneg (fun i hi => norm_nonneg _)
  change ∑ i, f i ≤ Real.sqrt (2/3)
  nlinarith [Real.sqrt_nonneg (2/3)]

private lemma sic_cmax_upper : cmax M_SIC ≤ Real.sqrt (2/3)/2 := by
  apply cmax_upper
  intro U hU
  let A := fun x => star U * M_SIC x * U
  have hA : IsPOVM A := conjugate_povm M_SIC sic_povm U hU
  refine (coh_le A _ (diag_incoherent A hA)).trans ?_
  rw [dephasing_distance A (fun x => (hA.1 x).isHermitian)]
  have h := sic_offdiag_sum_le U hU
  dsimp [A]
  linarith

private lemma upper_strict : Real.sqrt (2/3)/2 < (1/2:Real) := by
  have hs := Real.sq_sqrt (by norm_num : (0:Real) ≤ 2/3)
  nlinarith [Real.sqrt_nonneg (2/3)]

private lemma sic_bell_distance_lower (B : Fin 4 → (Matrix (Fin 4) (Fin 4) Complex)) (hB : IsIncoherent B) :
    (1/2:Real) ≤ dInf (fun x => star U_B * J (M_SIC x) * U_B) B := by
  have he (x : Fin 4) : (1/4:Real) ≤ ‖star U_B * J (M_SIC x) * U_B - B x‖ := by
    obtain ⟨v,w,hv,hw,hvA,hwA⟩ := sic_eigenvectors x
    have h := bell_effect_norm_lower (M_SIC x) (B x) (hB.2 x) 0 (1/2) v w hv hw (by norm_num at hvA ⊢; exact hvA)
      (by simpa using hwA)
    norm_num at h
    exact h
  unfold dInf
  have hsum : (1:Real) ≤ ∑ x, ‖star U_B * J (M_SIC x) * U_B - B x‖ := by
    calc 1 = ∑ x : Fin 4, (1/4:Real) := by norm_num
         _ ≤ _ := Finset.sum_le_sum (fun x hx => he x)
  linarith

private lemma sic_ancilla_cmax_lower : (1/2:Real) ≤ cmax (fun x => J (M_SIC x)) := by
  refine le_trans ?_ (coh_le_cmax (fun x => J (M_SIC x)) U_B bell_unitary)
  exact coh_lower _ (1/2) sic_bell_distance_lower

theorem result : ¬ claim := by
  intro h
  have hm := h 2 4 4 M_SIC J 1 (fun _ => (1/4:Real)) (by norm_num)
    sic_povm J_cp_unital (by norm_num) (by norm_num) (by intro x; norm_num)
    (by norm_num)
  simp only [Complex.ofReal_one, one_smul, sub_self, zero_mul, Complex.ofReal_zero,
    zero_smul, add_zero] at hm
  have hl := sic_ancilla_cmax_lower
  have hu := sic_cmax_upper
  have hs := upper_strict
  linarith


end D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone
