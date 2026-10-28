/- GID: D5/S3/QuantumChannels/ChannelTimeReversalNoGo
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/ChannelTimeReversalNoGo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: No randomisation-consistent channel symmetry reverses every unitary. -/
/- proof_shape: result: bind-only; consumers: none (settling result)
   escape_witness: none
   admission_basis: open-problem-resolution (#16378; Proved)
   Selected frozen dependencies (declaration statement_id, base e4cd4993c1aed7cf4dcbf1c93079e5ed0a892b37):
   D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.qubit_det_bounds [sha256:f4a0b109ad221dd8c74faf492e0239ab0bcfd7e1acf4dc75a9a7ad68be10324f]
   D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCPTP [sha256:1440f7e681ed2017e7c90aedfe54aa0ad218d57311655f9d554863853dd8f53c]
   D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.channel_cptp [sha256:12d1096835e803a33aaada5cb586f2c51f81dc4c2fe95a86cc39cb93d815a686]
   proof_shape: unitaryChannel: bind-only; escape_witness: none; consumers: Block.D, Block.D_apply, Part1Finish.Bi_basic, Part1Finish.R_swap, Part1Finite.B, Part1Finite.B_apply, Part1Finite.Bi, Part1Finite.Ti_apply, Part1Finite.Ti_cptp, Part1Finite.perm_action, Part1Finite.unitary_comp, Part1NoGo.Bi_mixture, Part1NoGo.Bi_reverse_trace, Part1NoGo.Bi_reversed, Part1NoGo.inverse_unitary_no_go, Part1NoGo.mixed_reverse_trace, Part1NoGo.reverse_trace, Part1NoGo.reversed_projection_trace, PauliChannels.D_cptp, PauliChannels.D_reverse_unitaries, PauliChannels.D_reversed, PauliChannels.D_two_unitaries, Qubit.Delta_cptp, Qubit.Delta_fixed, Qubit.Delta_pauli, QubitNoGo.forced_witness_output, QubitNoGo.inverse_unitary_no_go, QubitPreimage.preimage_replacement, QubitPreimage.pure_preimage, QubitRotation.pure_density_rotation, QubitUnital.J, QubitUnital.J_apply, QubitUnital.spinflip_cptp, QubitUnital.spinflip_double, QubitUnitalAction.unital_reversed, QubitWitness.B0_mixture, QubitWitness.conjugated_amplitude_identity, QubitWitness.conjugated_mixture, QubitWitness.conjugated_reverse, QubitWitness.fixed_witness_output, QubitWitness.unitary_delta, QubitWitness.unitary_unital, claim, kappa_unitary, kappa_unitary_transpose, result, transpose_target_reduces_to_star, unitaryChannel_cptp, unitary_channel_eq
   proof_shape: claim: bind-only; escape_witness: none; consumers: result (statement)
   proof_shape: unitary_channel_eq: bind-only; escape_witness: none; consumers: kappa_unitary
   proof_shape: kappa_unitary: bind-only; escape_witness: none; consumers: kappa_unitary_transpose
   proof_shape: kappa_unitary_transpose: bind-only; escape_witness: none; consumers: transpose_target_reduces_to_star
   proof_shape: transpose_target_reduces_to_star: bind-only; escape_witness: none; consumers: result
   proof_shape: unitaryChannel_cptp: bind-only; escape_witness: none; consumers: Part1Finite.Ti_cptp, Part1NoGo.mixed_reverse_trace, PauliChannels.D_cptp, PauliChannels.D_reversed, Qubit.Delta_cptp, Qubit.Delta_fixed, QubitNoGo.forced_witness_output, QubitNoGo.inverse_unitary_no_go, QubitUnital.spinflip_cptp, QubitWitness.conjugated_amplitude_identity, QubitWitness.conjugated_reverse, QubitWitness.unitary_delta
   proof_shape: Block.D: bind-only; escape_witness: none; consumers: Block.D_apply, Part1Finish.B_basic, Part1Finite.B_apply
   proof_shape: Block.D_apply: bind-only; escape_witness: none; consumers: Part1Finish.B_basic
   proof_shape: Part1Finite.perm_unitary: bind-only; escape_witness: none; consumers: Part1Finite.Ti_cptp, Part1NoGo.Bi_reverse_trace
   proof_shape: Part1Finite.perm_action: bind-only; escape_witness: none; consumers: Part1Finish.R_swap, Part1Finite.B_apply, Part1NoGo.reversed_projection_trace
   proof_shape: Part1Finite.unitary_comp: bind-only; escape_witness: none; consumers: Part1Finite.B_apply, Part1NoGo.Bi_mixture, QubitWitness.conjugated_mixture
   proof_shape: Part1Finite.B: bind-only; escape_witness: none; consumers: Part1Finish.B_basic, Part1Finish.Bi_basic, Part1Finite.B_apply, Part1Finite.Bi, Part1NoGo.Bi_mixture, Part1NoGo.reversed_projection_trace
   proof_shape: Part1Finite.B_apply: bind-only; escape_witness: none; consumers: Part1Finish.B_basic
   proof_shape: Part1Finite.Bi: bind-only; escape_witness: none; consumers: Part1Finish.Bi_basic, Part1NoGo.Bi_mixture, Part1NoGo.Bi_reverse_trace, Part1NoGo.Bi_reversed, Part1NoGo.inverse_unitary_no_go, Part1NoGo.reversed_projection_trace
   proof_shape: Part1Finite.Ti_apply: bind-only; escape_witness: none; consumers: Part1Finish.Bi_basic, Part1Finite.Ti_cptp
   proof_shape: Part1Finish.R_swap: bind-only; escape_witness: none; consumers: Part1Finish.Bi_basic
   proof_shape: Part1Finish.Bi_basic: bind-only; escape_witness: none; consumers: Part1NoGo.inverse_unitary_no_go
   proof_shape: Part1NoGo.reverse_trace: bind-only; escape_witness: none; consumers: Part1NoGo.mixed_reverse_trace
   proof_shape: Part1NoGo.mixed_reverse_trace: bind-only; escape_witness: none; consumers: Part1NoGo.Bi_reverse_trace
   proof_shape: Part1NoGo.Bi_mixture: bind-only; escape_witness: none; consumers: Part1NoGo.Bi_reverse_trace
   proof_shape: Part1NoGo.Bi_reverse_trace: bind-only; escape_witness: none; consumers: Part1NoGo.Bi_reversed
   proof_shape: Part1NoGo.Bi_reversed: bind-only; escape_witness: none; consumers: Part1NoGo.inverse_unitary_no_go
   proof_shape: Part1NoGo.inverse_unitary_no_go: bind-only; escape_witness: none; consumers: result
   proof_shape: Qubit.Delta_pauli: bind-only; escape_witness: none; consumers: Qubit.Delta_cptp, Qubit.Delta_fixed
   proof_shape: Qubit.Delta_cptp: bind-only; escape_witness: none; consumers: QubitNoGo.forced_witness_output, QubitPreimage.pure_preimage, QubitUnitalAction.unital_reversed
   proof_shape: Qubit.Delta_fixed: bind-only; escape_witness: none; consumers: QubitNoGo.forced_witness_output, QubitPreimage.pure_preimage, QubitUnitalAction.unital_reversed
   proof_shape: QubitUnital.J: bind-only; escape_witness: none; consumers: QubitPreimage.preimage_replacement, QubitUnital.J_apply, QubitUnital.spinflip_cptp, QubitUnital.spinflip_double, QubitUnital.unitalisation_action, QubitUnital.unitalisation_midpoint, QubitUnital.unitalisation_unital
   proof_shape: QubitUnital.J_apply: bind-only; escape_witness: none; consumers: QubitUnital.unitalisation_action
   proof_shape: QubitUnital.spinflip_double: bind-only; escape_witness: none; consumers: QubitUnital.spinflip_cptp
   proof_shape: QubitUnital.spinflip_cptp: bind-only; escape_witness: none; consumers: QubitPreimage.preimage_replacement
   proof_shape: PauliChannels.D_two_unitaries: bind-only; escape_witness: none; consumers: PauliChannels.D_cptp, PauliChannels.D_reversed
   proof_shape: PauliChannels.D_reverse_unitaries: bind-only; escape_witness: none; consumers: PauliChannels.D_reversed
   proof_shape: PauliChannels.D_reversed: bind-only; escape_witness: none; consumers: QubitUnitalAction.unital_reversed
   proof_shape: QubitPure.pure_output_replacement: bind-only; escape_witness: none; consumers: QubitPreimage.preimage_replacement
   proof_shape: QubitUnitalAction.coeff_bounds: bind-only; escape_witness: none; consumers: QubitUnitalAction.channel_pauli_expansion, QubitUnitalAction.weight_nonneg
   proof_shape: QubitUnitalAction.unital_reversed: bind-only; escape_witness: none; consumers: QubitPreimage.preimage_replacement
   proof_shape: QubitPreimage.preimage_replacement: bind-only; escape_witness: none; consumers: QubitPreimage.pure_preimage
   proof_shape: QubitPreimage.pure_preimage: bind-only; escape_witness: none; consumers: QubitNoGo.inverse_unitary_no_go
   proof_shape: QubitRotation.pure_density_rotation: bind-only; escape_witness: none; consumers: QubitNoGo.inverse_unitary_no_go
   proof_shape: QubitWitness.unitary_unital: bind-only; escape_witness: none; consumers: QubitWitness.unitary_delta
   proof_shape: QubitWitness.unitary_delta: bind-only; escape_witness: none; consumers: QubitWitness.conjugated_amplitude_identity
   proof_shape: QubitWitness.B0_mixture: bind-only; escape_witness: none; consumers: QubitWitness.conjugated_mixture
   proof_shape: QubitWitness.conjugated_mixture: bind-only; escape_witness: none; consumers: QubitWitness.conjugated_reverse
   proof_shape: QubitWitness.conjugated_reverse: bind-only; escape_witness: none; consumers: QubitNoGo.forced_witness_output
   proof_shape: QubitWitness.conjugated_amplitude_identity: bind-only; escape_witness: none; consumers: QubitNoGo.forced_witness_output
   proof_shape: QubitWitness.fixed_witness_output: bind-only; escape_witness: none; consumers: QubitNoGo.forced_witness_output
   proof_shape: QubitNoGo.forced_witness_output: bind-only; escape_witness: none; consumers: QubitNoGo.inverse_unitary_no_go
   proof_shape: QubitNoGo.inverse_unitary_no_go: bind-only; escape_witness: none; consumers: result
   Block.P_pos applies D5.S3.Quantum.Fibers.RankOneFeedbackProtocol.projector_positive.
   unitaryChannel is conjugation by U; claim uses it for both reversal targets.
   unitary_channel_eq identifies its body with Mathlib LinearMap.mulLeftRight.
   FiniteKrausRepresentation is unfrozen; the proof uses the frozen Kraus leaf and Mathlib.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16722
-/
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
import D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise
import D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
import D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
import D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsCPTP)
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli)
noncomputable section
namespace D5.S3.QuantumChannels.ChannelTimeReversalNoGo
def IsChannelSymmetry {d : ℕ} (S : MatrixMap (Fin d) (Fin d) ℂ → MatrixMap (Fin d) (Fin d) ℂ) : Prop :=
  Set.BijOn S {Φ | IsCPTP Φ} {Φ | IsCPTP Φ} ∧
    ∀ Φ Ψ, IsCPTP Φ → IsCPTP Ψ → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      S ((p : ℂ) • Φ + ((1 - p : ℝ) : ℂ) • Ψ) =
        (p : ℂ) • S Φ + ((1 - p : ℝ) : ℂ) • S Ψ
def unitaryChannel {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : MatrixMap (Fin d) (Fin d) ℂ := LinearMap.mulRight ℂ (star U) ∘ₗ LinearMap.mulLeft ℂ U
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ S, IsChannelSymmetry S →
    (¬ ∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) ∧
    (¬ ∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, S (unitaryChannel U) = unitaryChannel U.transpose)
variable {n m r : ℕ}
private lemma unitary_channel_eq {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    unitaryChannel U = LinearMap.mulLeftRight ℂ (U, star U) := by
  exact Matrix.ext_linearMap_iff.mpr (fun i => congrFun rfl)
private lemma kappa_isCPTP {d : ℕ} {Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) : IsCPTP ((fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) Phi) := by
  constructor
  · exact D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.cp_double_tau hPhi.1
  · intro X
    change (Matrix.transpose (Phi (Matrix.transpose X))).trace = X.trace; rw [Matrix.trace_transpose, hPhi.2]; rfl
private lemma kappa_involutive {d : ℕ} (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : (fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) ((fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) Phi) = Phi := by
  exact Matrix.ext_linearMap_iff.mpr (fun i => congrFun rfl)
private lemma kappa_symmetry {d : ℕ} : IsChannelSymmetry ((fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) (d := d)) := by
  constructor
  · constructor
    · intro Phi hPhi
      exact ⟨D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.cp_double_tau hPhi.1, fun X => by change (Matrix.transpose (Phi (Matrix.transpose X))).trace = X.trace; rw [Matrix.trace_transpose, hPhi.2]; rfl⟩
    · constructor
      · intro Phi hPhi Psi hPsi hEq
        have h := congrArg (fun (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) hEq; simpa only [kappa_involutive] using h
      · intro Psi hPsi
        refine ⟨(fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) Psi, kappa_isCPTP hPsi, ?_⟩; exact kappa_involutive Psi
  · intro Phi Psi hPhi hPsi p hp0 hp1
    ext X i j
    simp [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
private lemma kappa_unitary (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) : (fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) (unitaryChannel U) = unitaryChannel (star U.transpose) := by
  apply Eq.trans (congrArg
    (fun Phi : MatrixMap (Fin d) (Fin d) ℂ =>
      (Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap ∘ₗ Phi ∘ₗ
        (Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)
    (unitary_channel_eq U))
  apply Eq.trans ?_ (unitary_channel_eq (star U.transpose)).symm
  ext X i j
  simp [LinearMap.comp_apply, Matrix.transposeLinearEquiv, LinearMap.mulLeftRight_apply, Matrix.star_eq_conjTranspose, Matrix.transpose, Matrix.mul_apply, Matrix.conjTranspose_apply]; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a ha; apply Finset.sum_congr rfl; intro b hb; ring
private lemma kappa_unitary_transpose (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) : (fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) (unitaryChannel U.transpose) = unitaryChannel (star U) := by
  rw [kappa_unitary]
  congr 2
private lemma symmetry_comp {d : ℕ} {S T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)} (hS : IsChannelSymmetry S) (hT : IsChannelSymmetry T) : IsChannelSymmetry (T ∘ S) := by
  constructor
  · exact hT.1.comp hS.1
  · intro Phi Psi hPhi hPsi p hp0 hp1
    change T (S ((p : ℂ) • Phi + ((1-p : ℝ) : ℂ) • Psi)) = (p : ℂ) • T (S Phi) + ((1-p : ℝ) : ℂ) • T (S Psi)
    have hSPhi : IsCPTP (S Phi) := hS.1.1 hPhi
    have hSPsi : IsCPTP (S Psi) := hS.1.1 hPsi; rw [hS.2 Phi Psi hPhi hPsi p hp0 hp1]; rw [hT.2 (S Phi) (S Psi) hSPhi hSPsi p hp0 hp1]
private lemma transpose_target_reduces_to_star {d : ℕ} {S : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)} (hS : IsChannelSymmetry S) (hTarget : ∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, S (unitaryChannel U) = unitaryChannel U.transpose) : IsChannelSymmetry ((fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) (d := d) ∘ S) ∧
      (∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, ((fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) (d := d) ∘ S) (unitaryChannel U) = unitaryChannel (star U)) := by
  refine ⟨symmetry_comp hS (kappa_symmetry (d := d)), ?_⟩; intro U hU; change (fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) (S (unitaryChannel U)) = unitaryChannel (star U); rw [hTarget U hU, kappa_unitary_transpose]
private lemma cp_real_smul {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : Phi.IsCompletelyPositive) {p : ℝ} (hp : 0 ≤ p) : ((p : ℂ) • Phi).IsCompletelyPositive := by
  intro n A hA
  have hEq : MatrixMap.kron ((p : ℂ) • Phi) LinearMap.id A = p • (MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin n) (Fin n) ℂ) A) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    change MatrixMap.kron ((p : ℂ) • Phi) LinearMap.id A (i,a) (j,b) = (p : ℂ) * MatrixMap.kron Phi LinearMap.id A (i,a) (j,b); rw [MatrixMap.kron_def, MatrixMap.kron_def]; simp only [LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul]; simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hEq]; exact (hPhi n hA).smul hp
private lemma cptp_mix {d : ℕ} {Phi Psi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) (hPsi : IsCPTP Psi) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : IsCPTP ((p : ℂ) • Phi + ((1-p : ℝ) : ℂ) • Psi) := by
  constructor
  · exact (cp_real_smul hPhi.1 hp).add (cp_real_smul hPsi.1 (by linarith))
  · intro X
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Matrix.trace_add, Matrix.trace_smul, hPhi.2, hPsi.2]; push_cast; simp [sub_mul]
private lemma cptp_convex (d : ℕ) : Convex ℝ {Phi : MatrixMap (Fin d) (Fin d) ℂ | IsCPTP Phi} := by
  intro Phi hPhi Psi hPsi a b ha hb hab
  have hEq : b = 1-a := by linarith
  subst b; exact cptp_mix (p := a) hPhi hPsi ha (by linarith)
private lemma cptp_sum {d : ℕ} {ι : Type*} (s : Finset ι) (p : ι → ℝ) (Phi : ι → MatrixMap (Fin d) (Fin d) ℂ) (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) (hPhi : ∀ i ∈ s, IsCPTP (Phi i)) : IsCPTP (∑ i ∈ s, (p i : ℂ) • Phi i) := by
  exact (cptp_convex d).sum_mem hp hsum hPhi
private lemma finite_randomisation {d : ℕ} {S : MatrixMap (Fin d) (Fin d) ℂ → MatrixMap (Fin d) (Fin d) ℂ} (hS : IsChannelSymmetry S) {ι : Type*} (s : Finset ι) (p : ι → ℝ) (Phi : ι → MatrixMap (Fin d) (Fin d) ℂ) (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) (hPhi : ∀ i ∈ s, IsCPTP (Phi i)) : S (∑ i ∈ s, (p i : ℂ) • Phi i) = ∑ i ∈ s, (p i : ℂ) • S (Phi i) := by
  let G : Set ((MatrixMap (Fin d) (Fin d) ℂ) × (MatrixMap (Fin d) (Fin d) ℂ)) :=
    {z | IsCPTP z.1 ∧ z.2 = S z.1}
  have hG : Convex ℝ G := by
    intro x hx y hy a b ha hb hab
    have hEq : b = 1-a := by linarith
    subst b; refine ⟨cptp_mix (p := a) hx.1 hy.1 ha (by linarith), ?_⟩; change (a : ℂ) • x.2 + ((1-a : ℝ) : ℂ) • y.2 = S ((a : ℂ) • x.1 + ((1-a : ℝ) : ℂ) • y.1); rw [hx.2, hy.2, hS.2 x.1 y.1 hx.1 hy.1 a ha (by linarith)]
  have hmem := hG.sum_mem hp hsum (fun i hi => (show (Phi i, S (Phi i)) ∈ G from ⟨hPhi i hi, rfl⟩))
  have hpair : (∑ i ∈ s, p i • (Phi i, S (Phi i))) = (∑ i ∈ s, (p i : ℂ) • Phi i, ∑ i ∈ s, (p i : ℂ) • S (Phi i)) := by
    exact (prod_mk_sum s (fun i => (p i : ℂ) • Phi i) (fun i => (p i : ℂ) • S (Phi i))).symm
  rw [hpair] at hmem; exact hmem.2.symm
private lemma unitaryChannel_cptp {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) : IsCPTP (unitaryChannel U) := by
  constructor
  · let K : Fin 1 → Matrix (Fin d) (Fin d) ℂ := fun _ => U
    have heq : unitaryChannel U = MatrixMap.of_kraus K K := by
      ext X i j
      simp [unitaryChannel, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, MatrixMap.of_kraus, K, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.star_eq_conjTranspose]
    rw [heq]; exact MatrixMap.of_kraus_isCompletelyPositive K
  · intro X
    change Matrix.trace (U * X * star U) = Matrix.trace X; rw [Matrix.trace_mul_cycle U X (star U)]; rw [Matrix.star_eq_conjTranspose]
    have hstar : U.conjTranspose * U = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
    rw [hstar]; simp

namespace Block
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
private def Q (n : ℕ) : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n := Matrix.diagonal (fun i => if i.val < 3 then 0 else 1)
private def block (n : ℕ) (i : Fin (n+3)) : Fin 4 :=
  if i.val = 0 then 0 else if i.val = 1 then 1 else if i.val = 2 then 2 else 3
private def sign (s b : Fin 4) : ℂ :=
  if s.val = 0 then 1 else
  if s.val = 1 then D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.tetraX b else
  if s.val = 2 then D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.tetraY b else
  D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.tetraZ b
private def H (n : ℕ) (s : Fin 4) : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n := Matrix.diagonal (fun i => sign s (block n i))
private lemma sign_sq (s b : Fin 4) : star (sign s b) * sign s b = 1 := by
  fin_cases s <;> fin_cases b <;> norm_num [sign, D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.tetraX, D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.tetraY, D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.tetraZ, Fin.ext_iff]
private lemma sign_orthogonal (b c : Fin 4) : (1/4 : ℂ) * ∑ s : Fin 4, sign s b * star (sign s c) = if b = c then 1 else 0 := by
  simp only [Fin.sum_univ_succ]; fin_cases b <;> fin_cases c <;> norm_num [sign, D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.tetraX, D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.tetraY, D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.tetraZ, Fin.ext_iff]
private lemma H_unitary (n : ℕ) (s : Fin 4) : H n s ∈ Matrix.unitaryGroup (Fin (n+3)) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr; simp only [H, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]; rw [← Matrix.diagonal_one]
  congr 1
  funext i
  exact sign_sq s (block n i)
private def D (n : ℕ) : MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ :=
  (1/4 : ℂ) • ∑ s : Fin 4, unitaryChannel (H n s)
private lemma D_apply (n : ℕ) (X : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) (i j : Fin (n+3)) : D n X i j = if block n i = block n j then X i j else 0 := by
  simp only [D, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  have hentry (s : Fin 4) : unitaryChannel (H n s) X i j = (sign s (block n i) * star (sign s (block n j))) * X i j := by
    change (H n s * X * star (H n s)) i j = _; simp only [H, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]; ring
  simp_rw [hentry]; rw [← Finset.sum_mul, ← mul_assoc, sign_orthogonal]
  split_ifs <;> simp
private lemma P_pos (n : ℕ) (r : Fin 3) : ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n r).PosSemidef := by
  exact D5.S3.Quantum.Fibers.RankOneFeedbackProtocol.projector_positive
    (⟨r.val, by omega⟩ : Fin (n+3))
private lemma P_trace (n : ℕ) (r : Fin 3) : Matrix.trace ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n r) = 1 := by
  exact Matrix.trace_single_eq_same _ _
end Block
open Block
namespace Kraus
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
private lemma c_square : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = (1/2 : ℂ) := by
  simpa using congrArg (fun x : ℝ => (x : ℂ)) TsirelsonInequality.sqrt_two_inv_mul_self
private def KR (n : ℕ) : Fin 4 → (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n := ![(fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0 0, (fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0 1, (fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0 2, Q n]
private def KT (n : ℕ) : Fin 5 → (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n := ![(fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2 0, (fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 1, (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 2, (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2 2, Q n]
private def R (n : ℕ) : MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ := MatrixMap.of_kraus (KR n) (KR n)
private def T (n : ℕ) : MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ := MatrixMap.of_kraus (KT n) (KT n)
private lemma E_action (n : ℕ) (i j : Fin 3) (X : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) : (fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n i j * X * ((fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n i j).conjTranspose = X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n j) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n j) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n i := by
  simp [ Matrix.conjTranspose_single, Matrix.single_mul_mul_single, Matrix.smul_single]
private lemma Q_idempotent (n : ℕ) : Q n * Q n = Q n := by
  simp only [Q, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp
private lemma Q_star (n : ℕ) : (Q n).conjTranspose = Q n := by
  simp only [Q, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp [Pi.star_apply]
private lemma Q_complement (n : ℕ) : Q n = 1 - (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0 - (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 - (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Q, Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.single]; simp only [Matrix.of_apply, and_self, Fin.ext_iff]; change (if i.val < 3 then (0 : ℂ) else 1) = 1 - (if 0 = i.val then 1 else 0) - (if 1 = i.val then 1 else 0) - (if 2 = i.val then 1 else 0)
    by_cases h0 : 0 = i.val <;> by_cases h1 : 1 = i.val <;> by_cases h2 : 2 = i.val <;> simp only [h0, h1, h2, ↓reduceIte] <;> split_ifs <;> norm_num <;> omega
  · have hzero (k : Fin (n+3)) : ¬ (k = i ∧ k = j) := by rintro ⟨rfl,rfl⟩; exact hij rfl
    simp [Q, Matrix.diagonal_apply_ne _ hij, Matrix.single, hij, Matrix.one_apply_ne hij, hzero]
private lemma R_apply (n : ℕ) (X : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) : R n X = (X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) + X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 1) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 1) + X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2)) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0 + Q n * X * Q n := by
  simp only [R, MatrixMap.of_kraus, LinearMap.sum_apply]; simp only [Fin.sum_univ_succ, KR, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val', LinearMap.coe_mk, AddHom.coe_mk]; simp only [E_action, Q_star]; simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]; module
private lemma scaled_E_action (n : ℕ) (i j : Fin 3) (X : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) : ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n i j) * X * ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (fun (n : ℕ) (i j : Fin 3) => Matrix.single (⟨i.val, by omega⟩ : Fin (n+3)) (⟨j.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n i j).conjTranspose = (1/2 : ℂ) • (X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n j) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n j) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n i) := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, E_action]; rw [← mul_assoc, mul_comm (star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)) (((Real.sqrt 2 : ℝ) : ℂ)⁻¹), c_square]
private lemma T_apply (n : ℕ) (X : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) : T n X = X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2 + X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 1) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 1) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 + (X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2) / 2) • ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 + (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2) + Q n * X * Q n := by
  simp only [T, MatrixMap.of_kraus, LinearMap.sum_apply]; simp only [Fin.sum_univ_succ, KT, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val', LinearMap.coe_mk, AddHom.coe_mk]; simp only [scaled_E_action, E_action, Q_star]; simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]; module
private lemma Q_trace (n : ℕ) (X : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) : Matrix.trace (Q n * X * Q n) = Matrix.trace X - X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) - X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 1) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 1) - X ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2) := by
  rw [Matrix.trace_mul_cycle, Q_idempotent, Q_complement]; simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_single_mul, one_mul, one_smul]
private lemma R_cptp (n : ℕ) : IsCPTP (R n) := by
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive (KR n), ?_⟩; intro X; rw [R_apply, Matrix.trace_add, Matrix.trace_smul, P_trace, Q_trace]; ring
private lemma T_cptp (n : ℕ) : IsCPTP (T n) := by
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive (KT n), ?_⟩; intro X; rw [T_apply]; simp only [Matrix.trace_add, Matrix.trace_smul, P_trace, Q_trace]; ring
end Kraus
open Block Kraus
namespace Part1Finite
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
private def perm (n : ℕ) : Fin 3 → Equiv.Perm (Fin (n+3)) :=
  ![1, Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2) * Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 1), Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2)]
private lemma perm_unitary (n : ℕ) (p : Equiv.Perm (Fin (n+3))) : p.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin (n+3)) ℂ := by
  exact (D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.permutationUnitary p).property
private lemma perm_action (n : ℕ) (p : Equiv.Perm (Fin (n+3))) (X : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) : unitaryChannel (p.permMatrix ℂ) X = X.submatrix p p := by
  change p.permMatrix ℂ * X * star (p.permMatrix ℂ) = _; rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]; rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]; rfl
private lemma unitary_comp {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) : unitaryChannel (A * B) = unitaryChannel A ∘ₗ unitaryChannel B := by
  ext X i j
  simp [unitaryChannel, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, star_mul, Matrix.mul_assoc]
private def B (n : ℕ) : MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ :=
  (1/12 : ℂ) • ∑ k : Fin 3, ∑ s : Fin 4, unitaryChannel (((perm n k).permMatrix ℂ) * H n s)
private lemma B_apply (n : ℕ) (X : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) (i j : Fin (n+3)) : B n X i j = (1/3 : ℂ) * ∑ k : Fin 3, D n X (perm n k i) (perm n k j) := by
  have hcomp (k : Fin 3) (s : Fin 4) : unitaryChannel (((perm n k).permMatrix ℂ) * H n s) X i j = unitaryChannel (H n s) X (perm n k i) (perm n k j) := by
    rw [unitary_comp]; change unitaryChannel (((perm n k).permMatrix ℂ)) (unitaryChannel (H n s) X) i j = _; rw [ perm_action]; rfl
  simp only [B, Block.D, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]; simp_rw [hcomp, ← Finset.mul_sum]; ring
private def Bi (n : ℕ) (i : Fin 3) : MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ :=
  B n ∘ₗ unitaryChannel (((Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n i)).permMatrix ℂ))
private def Ti (n : ℕ) (i : Fin 3) : MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ :=
  MatrixMap.of_kraus (fun k => KT n k * ((Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n i)).permMatrix ℂ)) (fun k => KT n k * ((Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n i)).permMatrix ℂ))
private lemma Ti_apply (n : ℕ) (i : Fin 3) (X : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) : Ti n i X = T n (unitaryChannel (((Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n i)).permMatrix ℂ)) X) := by
  simp only [unitaryChannel, Ti, T, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]; apply Finset.sum_congr rfl; intro k hk; simp only [unitaryChannel, Matrix.conjTranspose_mul, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, Matrix.star_eq_conjTranspose]; simp [unitaryChannel, Matrix.mul_assoc]
private lemma Ti_cptp (n : ℕ) (i : Fin 3) : IsCPTP (Ti n i) := by
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive _, ?_⟩; intro X; rw [Ti_apply, (T_cptp n).2]; exact (unitaryChannel_cptp (perm_unitary n ((Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n i))))).2 X
private lemma diagonal_contradiction (n : ℕ) (A C0 C1 C2 : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) (hA : A.PosSemidef) (h0 : C0.PosSemidef) (h1 : C1.PosSemidef) (h2 : C2.PosSemidef) (htrace : Matrix.trace A = 1) (e0 : A + (2 : ℂ) • C0 = (2 : ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 + (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2) (e1 : A + (2 : ℂ) • C1 = (2 : ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0 + (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2) (e2 : A + (2 : ℂ) • C2 = (2 : ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 + (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0) : False := by
  have hdiag (i : Fin (n+3)) : A i i = 0 := by
    have ha := Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))
    have hc0 := (Complex.nonneg_iff.mp (h0.diag_nonneg (i := i))).1
    have hc1 := (Complex.nonneg_iff.mp (h1.diag_nonneg (i := i))).1
    have hc2 := (Complex.nonneg_iff.mp (h2.diag_nonneg (i := i))).1
    have he0 := congrArg (fun M : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n => (M i i).re) e0
    have he1 := congrArg (fun M : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n => (M i i).re) e1
    have he2 := congrArg (fun M : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n => (M i i).re) e2; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he0 he1 he2; norm_num at he0 he1 he2; apply Complex.ext
    · change (A i i).re = 0
      by_cases hpi0 : i = (fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0
      · subst i
        simp [ Matrix.single, Fin.ext_iff] at he0; norm_num []; norm_num [] at ha hc0
        linarith [ha.1]
      · by_cases hpi1 : i = (fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 1
        · subst i
          simp [ Matrix.single, Fin.ext_iff] at he1; norm_num []; norm_num [] at ha hc1
          linarith [ha.1]
        · by_cases hpi2 : i = (fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2
          · subst i
            simp [ Matrix.single, Fin.ext_iff] at he2; norm_num []; norm_num [] at ha hc2
            linarith [ha.1]
          · have hv1 : i.val ≠ 1 := by
              intro hh; apply hpi1; apply Fin.ext; exact hh
            have hv2 : i.val ≠ 2 := by
              intro hh; apply hpi2; apply Fin.ext; exact hh
            simp [Matrix.single, Fin.ext_iff, Ne.symm hv1, Ne.symm hv2] at he0
            linarith [ha.1]
    · simpa using ha.2.symm
  have ht : Matrix.trace A = 0 := by
    simp [Matrix.trace, Matrix.diag, hdiag]
  rw [ht] at htrace; norm_num at htrace
end Part1Finite
open Block Kraus Part1Finite
namespace Part1Finish
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
private lemma index_cases (n : ℕ) (i : Fin (n+3)) : i = (fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0 ∨ i = (fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 1 ∨ i = (fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2 ∨ 3 ≤ i.val := by
  by_cases h0 : i = (fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0
  · exact Or.inl h0
  by_cases h1 : i = (fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : i = (fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 2
  · exact Or.inr (Or.inr (Or.inl h2))
  right; right; right
  simp only [Fin.ext_iff] at h0 h1 h2
  omega
private lemma B_basic (n : ℕ) : B n = (1/3 : ℂ) • R n + (2/3 : ℂ) • T n := by
  ext X i j
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, B_apply, R_apply, T_apply]
  rcases index_cases n i with rfl | rfl | rfl | hi <;> rcases index_cases n j with rfl | rfl | rfl | hj
  all_goals
    simp [-Fin.val_eq_zero_iff, Fin.sum_univ_three, D_apply, perm, Equiv.swap_apply_def, block, Fin.ext_iff, Matrix.single, Q, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> try ring
  all_goals
    try have hi3 : ¬ i.val < 3 := by exact Nat.not_lt.mpr hi
    try have hj3 : ¬ j.val < 3 := by exact Nat.not_lt.mpr hj
    try have hi0 : i.val ≠ 0 := by exact Nat.ne_zero_of_lt hi
    try have hi1 : i.val ≠ 1 := by omega
    try have hi2 : i.val ≠ 2 := by exact (Nat.ne_of_lt hi).symm
    try have hj0 : j.val ≠ 0 := by exact Nat.ne_zero_of_lt hj
    try have hj1 : j.val ≠ 1 := by omega
    try have hj2 : j.val ≠ 2 := by exact (Nat.ne_of_lt hj).symm
    simp_all [-Fin.val_eq_zero_iff, Fin.ext_iff, eq_comm] <;> try ring
  all_goals split_ifs <;> first | omega | rfl
private lemma R_swap (n : ℕ) (r : Fin 3) : R n ∘ₗ unitaryChannel (((Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n r)).permMatrix ℂ)) = R n := by
  ext X i j
  simp only [LinearMap.comp_apply, perm_action, R_apply]; fin_cases r
  all_goals
    rcases index_cases n i with rfl | rfl | rfl | hi <;> rcases index_cases n j with rfl | rfl | rfl | hj
  all_goals
    simp [-Fin.val_eq_zero_iff, Equiv.swap_apply_def, Fin.ext_iff, Matrix.single, Q, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv] <;> try ring
  all_goals
    try have hi3 : ¬ i.val < 3 := by exact Nat.not_lt.mpr hi
    try have hj3 : ¬ j.val < 3 := by exact Nat.not_lt.mpr hj
    try have hi0 : i.val ≠ 0 := by exact Nat.ne_zero_of_lt hi
    try have hi1 : i.val ≠ 1 := by omega
    try have hi2 : i.val ≠ 2 := by exact (Nat.ne_of_lt hi).symm
    try have hj0 : j.val ≠ 0 := by exact Nat.ne_zero_of_lt hj
    try have hj1 : j.val ≠ 1 := by omega
    try have hj2 : j.val ≠ 2 := by exact (Nat.ne_of_lt hj).symm
    simp_all [-Fin.val_eq_zero_iff, Fin.ext_iff, eq_comm] <;> try ring
private lemma Bi_basic (n : ℕ) (r : Fin 3) : Bi n r = (1/3 : ℂ) • R n + (2/3 : ℂ) • Ti n r := by
  ext X i j
  change B n (unitaryChannel (((Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n r)).permMatrix ℂ)) X) i j = _; rw [B_basic]
  have hr := congrArg (fun F => F X) (R_swap n r); simp only [LinearMap.comp_apply] at hr; simp only [LinearMap.add_apply, LinearMap.smul_apply, Ti_apply, LinearMap.comp_apply, hr]
end Part1Finish
open Block Kraus Part1Finite Part1Finish
namespace Part1NoGo
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
private lemma reverse_trace {d : ℕ} (U X Y : Matrix (Fin d) (Fin d) ℂ) : Matrix.trace (unitaryChannel (star U) X * Y) = Matrix.trace (X * unitaryChannel U Y) := by
  change Matrix.trace (star U * X * star (star U) * Y) = Matrix.trace (X * (U * Y * star U)); simpa only [star_star, Matrix.mul_assoc] using Matrix.trace_mul_comm (star U) (X * U * Y)
private lemma mixed_reverse_trace {d : ℕ} {S : MatrixMap (Fin d) (Fin d) ℂ → MatrixMap (Fin d) (Fin d) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) {ι : Type*} (s : Finset ι) (p : ι → ℝ) (U : ι → Matrix (Fin d) (Fin d) ℂ) (hp : ∀ k ∈ s, 0 ≤ p k) (hs : ∑ k ∈ s, p k = 1) (hu : ∀ k ∈ s, U k ∈ Matrix.unitaryGroup (Fin d) ℂ) (X Y : Matrix (Fin d) (Fin d) ℂ) : Matrix.trace (S (∑ k ∈ s, (p k : ℂ) • unitaryChannel (U k)) X * Y) = Matrix.trace (X * (∑ k ∈ s, (p k : ℂ) • unitaryChannel (U k)) Y) := by
  rw [finite_randomisation hS s p _ hp hs (fun k hk => unitaryChannel_cptp (hu k hk))]; simp only [LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul]; apply Finset.sum_congr rfl; intro k hk; rw [ht _ (hu k hk), reverse_trace]
private lemma Bi_mixture (n : ℕ) (r : Fin 3) : Bi n r = ∑ ks : Fin 3 × Fin 4, (1/12 : ℂ) • unitaryChannel ((((perm n ks.1).permMatrix ℂ) * H n ks.2) * ((Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n r)).permMatrix ℂ)) := by
  ext X i j
  simp [Bi, B, Fintype.sum_prod_type, unitary_comp, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Matrix.mul_assoc]
private lemma Bi_reverse_trace (n : ℕ) (r : Fin 3) {S : MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ → MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin (n+3)) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) (X Y : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) : Matrix.trace (S (Bi n r) X * Y) = Matrix.trace (X * Bi n r Y) := by
  rw [Bi_mixture]
  have hh := mixed_reverse_trace hS ht (Finset.univ : Finset (Fin 3 × Fin 4)) (fun _ => (1/12:ℝ)) (fun ks => (((perm n ks.1).permMatrix ℂ) * H n ks.2) * ((Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n r)).permMatrix ℂ)) (by intro ks hks; norm_num) (by norm_num) (by
      intro ks hks; exact (Matrix.unitaryGroup _ _).mul_mem ((Matrix.unitaryGroup _ _).mul_mem (perm_unitary n (perm n ks.1)) (H_unitary n ks.2)) (perm_unitary n ((Equiv.swap ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n 0) ((fun (n : ℕ) (r : Fin 3) => (⟨r.val, by omega⟩ : Fin (n+3))) n r))))) X Y
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hh
private def reversed_projection (n : ℕ) (r : Fin 3) : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n :=
  ![(2/3 : ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 + (1/3 : ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2, (2/3 : ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0 + (1/3 : ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2, (2/3 : ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 + (1/3 : ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0] r
private lemma reversed_projection_trace (n : ℕ) (r : Fin 3) (X : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n) : Matrix.trace ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 * Bi n r X) = Matrix.trace (reversed_projection n r * X) := by
  simp only [ Matrix.trace_single_mul, one_mul, Bi, LinearMap.comp_apply]; rw [B_basic]; simp only [LinearMap.add_apply, LinearMap.smul_apply, R_apply, T_apply]; fin_cases r
  · change _ = Matrix.trace (((2/3:ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 + (1/3:ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2) * X)
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul, one_mul, perm_action]; simp [-Fin.val_eq_zero_iff, Equiv.swap_apply_def, Fin.ext_iff, Matrix.single, Q, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]; ring
  · change _ = Matrix.trace (((2/3:ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0 + (1/3:ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 2) * X)
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul, one_mul, perm_action]; simp [-Fin.val_eq_zero_iff, Equiv.swap_apply_def, Fin.ext_iff, Matrix.single, Q, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]; ring
  · change _ = Matrix.trace (((2/3:ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 + (1/3:ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0) * X)
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul, one_mul, perm_action]; simp [-Fin.val_eq_zero_iff, Equiv.swap_apply_def, Fin.ext_iff, Matrix.single, Q, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]; ring
private lemma Bi_reversed (n : ℕ) (r : Fin 3) {S : MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ → MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin (n+3)) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) : S (Bi n r) ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1) = reversed_projection n r := by
  apply Matrix.ext_iff_trace_mul_right.mpr; intro X; rw [Bi_reverse_trace n r hS ht, reversed_projection_trace]
private theorem inverse_unitary_no_go (n : ℕ) {S : MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ → MatrixMap (Fin (n+3)) (Fin (n+3)) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin (n+3)) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) : False := by
  have hR : IsCPTP (S (R n)) := hS.1.1 (R_cptp n)
  have hT (r : Fin 3) : IsCPTP (S (Ti n r)) := hS.1.1 (Ti_cptp n r)
  have he (r : Fin 3) : S (R n) ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1) + (2:ℂ) • S (Ti n r) ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1) = (3:ℂ) • reversed_projection n r := by
    have hm := hS.2 (R n) (Ti n r) (R_cptp n) (Ti_cptp n r) (1/3) (by norm_num) (by norm_num); norm_num at hm; rw [← Bi_basic] at hm
    have hx := congrArg (fun F => F ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1)) hm; simp only [LinearMap.add_apply, LinearMap.smul_apply] at hx; rw [Bi_reversed n r hS ht] at hx
    ext i j
    have hej := congrArg (fun M : (fun n : ℕ => Matrix (Fin (n+3)) (Fin (n+3)) ℂ) n => M i j) hx; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hej ⊢; linear_combination -3 * hej
  apply diagonal_contradiction n (S (R n) ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1)) (S (Ti n 0) ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1)) (S (Ti n 1) ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1)) (S (Ti n 2) ((fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1))
  · exact (fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) hR (P_pos n 1)
  · exact (fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) (hT 0) (P_pos n 1)
  · exact (fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) (hT 1) (P_pos n 1)
  · exact (fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) (hT 2) (P_pos n 1)
  · rw [hR.2, P_trace]
  · have hh := he 0
    norm_num [reversed_projection, smul_add, smul_smul, Matrix.smul_single] at hh ⊢; exact hh
  · have hh := he 1
    norm_num [reversed_projection, smul_add, smul_smul, Matrix.smul_single] at hh ⊢; exact hh
  · have hh := he 2
    change _ = (3:ℂ) • ((2/3:ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 1 + (1/3:ℂ) • (fun (n : ℕ) (r : Fin 3) => Matrix.single (⟨r.val, by omega⟩ : Fin (n+3)) (⟨r.val, by omega⟩ : Fin (n+3)) (1 : ℂ)) n 0) at hh; norm_num [reversed_projection, smul_add, smul_smul, Matrix.smul_single] at hh ⊢; exact hh
end Part1NoGo
namespace Qubit
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
private lemma sigma_star (r : Fin 3) : star (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli r) = D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli r := by
  simpa only [D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli, Matrix.star_eq_conjTranspose] using D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian (![Pauli.X, Pauli.Y, Pauli.Z] r)
private lemma sigma_square (r : Fin 3) : D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli r * D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli r = 1 := by
  simpa only [D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli] using D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.pauli_square (![Pauli.X, Pauli.Y, Pauli.Z] r)
private lemma sigma_unitary (r : Fin 3) : D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli r ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr; rw [sigma_star, sigma_square]
private lemma Delta_pauli : (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) = (1/4 : ℂ) • (unitaryChannel 1 + unitaryChannel (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 0) + unitaryChannel (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 1) + unitaryChannel (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 2)) := by
  ext X i j
  fin_cases i <;> fin_cases j <;> simp [unitaryChannel,  D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli, pauliMatrix, qubitX, qubitZ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Pi.star_apply, map_inv₀, map_ofNat, Fin.sum_univ_two, Complex.I_mul_I] <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring
private lemma Delta_cptp : IsCPTP (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) := by
  let U : Fin 4 → QubitMatrix := ![1, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 0, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 1, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 2]
  have hU : ∀ i, U i ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    intro i; fin_cases i <;> simp only [U, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · exact (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
    · exact sigma_unitary 0
    · exact sigma_unitary 1
    · exact sigma_unitary 2
  have h := cptp_sum (Finset.univ : Finset (Fin 4)) (fun _ => (1/4 : ℝ)) (fun i => unitaryChannel (U i)) (by intro i hi; norm_num) (by norm_num) (by intro i hi; exact unitaryChannel_cptp (hU i)); rw [Delta_pauli]; simpa [U, Fin.sum_univ_succ, Finset.smul_sum, add_assoc] using h
private lemma Delta_fixed {S : MatrixMap (Fin 2) (Fin 2) ℂ → MatrixMap (Fin 2) (Fin 2) ℂ} (hS : IsChannelSymmetry S) (hTarget : ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) : S (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) = (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) := by
  let U : Fin 4 → QubitMatrix := ![1, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 0, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 1, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 2]
  have hU : ∀ i, U i ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    intro i; fin_cases i <;> simp only [unitaryChannel, U, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · exact (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
    · exact sigma_unitary 0
    · exact sigma_unitary 1
    · exact sigma_unitary 2
  have h := finite_randomisation hS (Finset.univ : Finset (Fin 4)) (fun _ => (1/4 : ℝ)) (fun i => unitaryChannel (U i)) (by intro i hi; norm_num) (by norm_num) (by intro i hi; exact unitaryChannel_cptp (hU i))
  have hstar : ∀ i, star (U i) = U i := by
    intro i; fin_cases i <;> simp [unitaryChannel, U, sigma_star]
  simp_rw [hTarget _ (hU _), hstar] at h
  have hmix : (∑ i : Fin 4, ((1/4 : ℝ) : ℂ) • unitaryChannel (U i)) = (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) := by
    rw [Delta_pauli]; simp [unitaryChannel, U, Fin.sum_univ_succ, Finset.smul_sum, add_assoc]
  simpa only [hmix] using h
lemma pauli_expansion (X : QubitMatrix) : X = (Matrix.trace X / 2) • (1 : QubitMatrix) + ∑ b : Fin 3, (Matrix.trace (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b * X) / 2) • D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b := by
  let Y : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ := fun i j => X (i 0) (j 0)
  have ht (p : Pauli) : Matrix.trace (wordOp (fun _ : Fin 1 => p) * Y) = Matrix.trace (pauliMatrix p * X) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      ← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin 2)).symm]
    simp [wordOp, tensorOp, Y, Equiv.funUnique, Equiv.piUnique]
  have h := D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.word_expansion Y
  ext i j
  have he := congrArg (fun M => M (fun _ => i) (fun _ => j)) h
  simp only [Matrix.sum_apply, Matrix.smul_apply,
    ← Equiv.sum_comp (Equiv.funUnique (Fin 1) Pauli).symm] at he
  have hfun (p : Pauli) : (Equiv.funUnique (Fin 1) Pauli).symm p = fun _ => p := by
    exact (Equiv.symm_apply_eq _).mpr rfl
  simp only [pow_one, hfun] at he
  simp only [ht] at he
  simp [Y, wordOp, tensorOp, pauli, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sum_apply, Fin.sum_univ_three,
    div_eq_mul_inv, mul_comm] at he ⊢
  have hu : (Finset.univ : Finset Pauli) = {.I, .X, .Y, .Z} := by exact Finset.val_inj.mp rfl
  rw [hu] at he
  simpa [pauliMatrix, add_assoc] using he

private def p4 : Fin 4 → ℝ := ![9/16,3/16,3/16,1/16]
private def A0 : MatrixMap (Fin 2) (Fin 2) ℂ := MatrixMap.of_kraus
  (fun j : Fin 2 => D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation.amplitudeKraus (K := 1) j (3/4))
  (fun j : Fin 2 => D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation.amplitudeKraus (K := 1) j (3/4))
private lemma damping_zero : D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation.amplitudeKraus (K := 1) 0 (3/4) = (!![1,0;0,1/2] : QubitMatrix) := by
  have hs : Real.sqrt (1/4) = 1/2 := by
    rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation.amplitudeKraus, hs]
private lemma damping_one : D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation.amplitudeKraus (K := 1) 1 (3/4) = ((Real.sqrt 3 : ℝ) / 2 : ℂ) • Matrix.single 0 1 1 := by
  have hs : Real.sqrt (3/4) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_div (by norm_num)]; norm_num
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation.amplitudeKraus, Matrix.single, hs]
private lemma sqrt3sq : ((Real.sqrt 3 : ℝ) : ℂ)^2 = 3 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)
private lemma A0_apply (X : QubitMatrix) : A0 X = !![X 0 0 + 3/4 * X 1 1, X 0 1 / 2; X 1 0 / 2, X 1 1 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A0, MatrixMap.of_kraus, damping_zero, damping_one, Matrix.single, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Pi.star_apply, map_inv₀, map_ofNat, Fin.sum_univ_two, Complex.star_def, map_div₀, Complex.conj_ofReal] <;> ring_nf <;> norm_num [sqrt3sq] <;> ring
private lemma A0_cptp : IsCPTP A0 := by
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive _, ?_⟩; intro X; rw [A0_apply]; simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]; ring
private lemma amplitude_damping_identity : A0 = (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel p4) + (3/4 : ℂ) • (((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single 0 0 1) - (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2)) := by
  ext X i j
  rw [A0_apply]; fin_cases i <;> fin_cases j <;> simp [p4, D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel, D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma, Fin.sum_univ_succ,   D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli, pauliMatrix, qubitX, qubitZ, Matrix.single, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Pi.star_apply, map_inv₀, map_ofNat, Fin.sum_univ_two, Complex.I_mul_I] <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring
end Qubit
open Qubit
namespace QubitUnital
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def J : MatrixMap (Fin 2) (Fin 2) ℂ := unitaryChannel (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 1) ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)
lemma J_apply (X : QubitMatrix) : J X = Matrix.trace X • (1 : QubitMatrix) - X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitaryChannel, J, Matrix.transposeLinearEquiv, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli, pauliMatrix, qubitX, qubitZ, Matrix.transpose, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Fin.sum_univ_two] <;> try ring_nf <;> norm_num [Complex.I_sq] <;> ring
private lemma spinflip_double (Phi : MatrixMap (Fin 2) (Fin 2) ℂ) : J ∘ₗ Phi ∘ₗ J = unitaryChannel (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 1) ∘ₗ (fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) Phi ∘ₗ unitaryChannel (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 1) := by
  ext X i j
  simp only [unitaryChannel, J, LinearMap.comp_apply, LinearMap.comp_apply]
  have hcomm (Y : QubitMatrix) : ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) (unitaryChannel (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 1) Y) = unitaryChannel (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 1) (((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) Y) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [unitaryChannel, Matrix.transposeLinearEquiv, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli, pauliMatrix, qubitX, qubitZ, Matrix.transpose, Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Fin.sum_univ_two] <;> try ring_nf <;> norm_num [Complex.I_sq] <;> ring
  simp only [unitaryChannel, LinearMap.comp_apply] at hcomm
  rw [hcomm]
private lemma spinflip_cptp (Phi : MatrixMap (Fin 2) (Fin 2) ℂ) (hPhi : IsCPTP Phi) : IsCPTP (J ∘ₗ Phi ∘ₗ J) := by
  rw [spinflip_double]
  have hu := unitaryChannel_cptp (sigma_unitary 1)
  have hk := kappa_isCPTP hPhi
  constructor
  · exact D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.cp_comp hu.1
      (D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.cp_comp hk.1 hu.1)
  · intro X
    change Matrix.trace (unitaryChannel (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 1) ((fun {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) => ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap) ∘ₗ Phi ∘ₗ ((Matrix.transposeLinearEquiv _ _ ℂ ℂ).toLinearMap)) Phi (unitaryChannel (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 1) X))) = X.trace
    rw [hu.2, hk.2, hu.2]
private lemma unitalisation_action (Phi : MatrixMap (Fin 2) (Fin 2) ℂ) (hPhi : IsCPTP Phi) (X : QubitMatrix) : (J ∘ₗ Phi ∘ₗ J) X = Phi X + Matrix.trace X • (1 - Phi 1) := by
  simp only [LinearMap.comp_apply, J_apply, map_sub, map_smul, hPhi.2]; simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]; module
private lemma unitalisation_midpoint (Phi : MatrixMap (Fin 2) (Fin 2) ℂ) (hPhi : IsCPTP Phi) : (1/2 : ℂ) • (Phi + J ∘ₗ Phi ∘ₗ J) = Phi - ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) ((1/2 : ℂ) • Phi 1) + (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) := by
  ext X i j
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, unitalisation_action Phi hPhi X, D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply,  LinearMap.coe_mk, AddHom.coe_mk]; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
private lemma unitalisation_unital (Phi : MatrixMap (Fin 2) (Fin 2) ℂ) (hPhi : IsCPTP Phi) : ((1/2 : ℂ) • (Phi + J ∘ₗ Phi ∘ₗ J)) 1 = 1 := by
  rw [unitalisation_midpoint Phi hPhi]
  ext i j
  simp [D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply,  Matrix.trace_one, Fintype.card_fin, smul_smul]
private lemma density_cayley_hamilton (rho : QubitMatrix) (htr : Matrix.trace rho = 1) : rho * rho - rho + Matrix.det rho • 1 = 0 := by
  have h := rho.aeval_self_charpoly
  rw [Matrix.charpoly_fin_two, htr] at h
  simpa [Polynomial.aeval_def, pow_two, Algebra.smul_def] using h
end QubitUnital
open Qubit QubitUnital
namespace PauliChannels
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
lemma density_psd (a : Fin 3) (e : Bool) : ((fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) a e).PosSemidef := by
  have hp : (![Pauli.X, Pauli.Y, Pauli.Z] a) ≠ Pauli.I := by fin_cases a <;> decide
  obtain ⟨_, U, _, _, _, _, _, hEq⟩ := D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral_stabilizer (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0) hp
  dsimp only; rw [hEq]; exact Matrix.posSemidef_vecMulVec_self_star _
lemma sigma_trace (a : Fin 3) : Matrix.trace (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli a) = 0 := by
  have h := D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_trace_pair (![Pauli.X, Pauli.Y, Pauli.Z] a) Pauli.I
  fin_cases a <;> simpa [D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli, pauliMatrix] using h
lemma density_trace (a : Fin 3) (e : Bool) : Matrix.trace ((fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) a e) = 1 := by
  exact D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.pauli_projector_trace _ (by fin_cases a <;> decide) e
private def L (a b : Fin 3) : MatrixMap (Fin 2) (Fin 2) ℂ :=
  ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).comp (LinearMap.mulLeft ℂ (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b))).smulRight ((1/2 : ℂ) • D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli a)
private def D (a b : Fin 3) (e : Bool) : MatrixMap (Fin 2) (Fin 2) ℂ :=
  (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) + (if e then -1 else 1 : ℂ) • L a b
private lemma r_square : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)^2 = (1/2 : ℂ) := by
  simpa only [pow_two, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat, one_div] using congrArg (fun x : ℝ => (x : ℂ)) TsirelsonInequality.sqrt_two_inv_mul_self
private lemma I_five : Complex.I^5 = Complex.I := by rw [Complex.I_pow_eq_pow_mod]; norm_num
private lemma I_six : Complex.I^6 = -1 := by rw [Complex.I_pow_eq_pow_mod]; norm_num [r_square, Complex.I_sq]
private def W (a b : Fin 3) : QubitMatrix := if a = b then 1 else (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli a + D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b)
private def flip (a : Fin 3) : Fin 3 := if a = 0 then 1 else 0
private def G (a b : Fin 3) (e : Bool) : QubitMatrix :=
  if e then D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli (flip a) * W a b else W a b
private lemma G_unitary (a b : Fin 3) (e : Bool) : G a b e ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  cases e <;> fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [G, W, flip, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Pi.star_apply, map_inv₀, map_ofNat, Fin.sum_univ_two, Complex.I_mul_I] <;> try ring_nf <;> norm_num [r_square, Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four, I_five, I_six] <;> try ring_nf <;> norm_num [r_square, Complex.I_sq, Complex.I_pow_three] <;> try ring
  all_goals norm_num only [r_square] <;> ring

private lemma D_two_unitaries (a b : Fin 3) (e : Bool) : D a b e = (1/2 : ℂ) • (unitaryChannel (G a b e) + unitaryChannel (G a b e * D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b)) := by
  ext X i j
  cases e <;> fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> simp [unitaryChannel, PauliChannels.D, D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral, L,  D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, G, W, flip, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli, pauliMatrix, qubitX, qubitZ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Pi.star_apply, map_inv₀, map_ofNat, Fin.sum_univ_two, Complex.I_mul_I] <;> try ring_nf <;> norm_num [r_square, Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four, I_five, I_six] <;> try ring_nf <;> norm_num [r_square, Complex.I_sq, Complex.I_pow_three] <;> try ring
  all_goals norm_num only [r_square] <;> ring

private lemma D_reverse_unitaries (a b : Fin 3) (e : Bool) : (1/2 : ℂ) • (unitaryChannel (star (G a b e)) + unitaryChannel (star (G a b e * D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b))) = D b a e := by
  ext X i j
  cases e <;> fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> simp [unitaryChannel, PauliChannels.D, D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral, L,  D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, G, W, flip, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli, pauliMatrix, qubitX, qubitZ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Pi.star_apply, map_inv₀, map_ofNat, Fin.sum_univ_two, Complex.I_mul_I] <;> try ring_nf <;> norm_num [r_square, Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four, I_five, I_six] <;> try ring_nf <;> norm_num [r_square, Complex.I_sq, Complex.I_pow_three] <;> try ring
  all_goals norm_num only [r_square] <;> ring

private lemma D_cptp (a b : Fin 3) (e : Bool) : IsCPTP (D a b e) := by
  rw [D_two_unitaries]
  have hu := unitaryChannel_cptp (G_unitary a b e)
  have hv := unitaryChannel_cptp ((Matrix.unitaryGroup _ _).mul_mem (G_unitary a b e) (sigma_unitary b))
  convert cptp_mix (p := (1/2:ℝ)) hu hv (by norm_num) (by norm_num) using 1 <;> norm_num <;> module
private lemma D_reversed {S : MatrixMap (Fin 2) (Fin 2) ℂ → MatrixMap (Fin 2) (Fin 2) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) (a b : Fin 3) (e : Bool) : S (D a b e) = D b a e := by
  rw [D_two_unitaries]
  have hg := G_unitary a b e
  have hgs := (Matrix.unitaryGroup _ _).mul_mem hg (sigma_unitary b)
  have heq := hS.2 _ _ (unitaryChannel_cptp hg) (unitaryChannel_cptp hgs) (1/2) (by norm_num) (by norm_num); norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, sub_half] at heq
  have hm : (1/2 : ℂ) • (unitaryChannel (G a b e) + unitaryChannel (G a b e * D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b)) = (1/2 : ℂ) • unitaryChannel (G a b e) + (1/2 : ℂ) • unitaryChannel (G a b e * D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b) := by exact smul_add _ _ _
  rw [hm, heq, ht _ hg, ht _ hgs]; rw [← smul_add, D_reverse_unitaries]
end PauliChannels
open Qubit QubitUnital PauliChannels
namespace QubitPure
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
private lemma replacement_cptp (rho : QubitMatrix) (hρ : rho.PosSemidef) (htr : Matrix.trace rho = 1) : IsCPTP (((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) rho) := by
  constructor
  · obtain ⟨C, hc⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
    let K : Fin 2 × Fin 2 → QubitMatrix := fun ij =>
      C.conjTranspose * Matrix.single ij.1 ij.2 1
    have he : ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) rho = MatrixMap.of_kraus K K := by
      rw [hc]
      ext X i j
      fin_cases i <;> fin_cases j <;> simp [D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, MatrixMap.of_kraus, K, Fintype.sum_prod_type, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Matrix.single, Matrix.trace, Matrix.diag, Fin.sum_univ_two] <;> ring
    rw [he]; exact MatrixMap.of_kraus_isCompletelyPositive K
  · intro X
    simp [D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.trace_smul, htr]
private lemma psd_zero_corner (M : QubitMatrix) (hM : M.PosSemidef) (hz : M 0 0 = 0) : M = Matrix.trace M • Matrix.single 1 1 1 := by
  have hq : dotProduct (star (Pi.single (0 : Fin 2) (1 : ℂ))) (Matrix.mulVec M (Pi.single 0 1)) = 0 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hz]
  have hc := hM.dotProduct_mulVec_zero_iff.mp hq
  have h10 : M 1 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hc 1
  have h01 : M 0 1 = 0 := by
    have he := hM.isHermitian.apply 0 1; simpa [h10] using he.symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.single, hz, h10, h01]
private lemma bounded_pure_output (C : MatrixMap (Fin 2) (Fin 2) ℂ) (hC : IsCPTP C) (hone : C 1 = (2 : ℂ) • Matrix.single 1 1 1) (X : QubitMatrix) (hX : X.PosSemidef) (hcomp : (1-X).PosSemidef) : C X = Matrix.trace X • Matrix.single 1 1 1 := by
  have hx := (fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) hC hX
  have hc := (fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) hC hcomp
  have hge := (Complex.nonneg_iff.mp (hx.diag_nonneg (i := 0))).1
  have hle := (Complex.nonneg_iff.mp (hc.diag_nonneg (i := 0))).1
  have him := (Complex.nonneg_iff.mp (hx.diag_nonneg (i := 0))).2
  have hz : C X 0 0 = 0 := by
    apply Complex.ext
    · simp [map_sub, hone, Matrix.single] at hle
      change (C X 0 0).re = 0
      linarith
    · simpa using him.symm
  rw [psd_zero_corner _ hx hz, hC.2]
private lemma pure_output_replacement (C : MatrixMap (Fin 2) (Fin 2) ℂ) (hC : IsCPTP C) (hone : C 1 = (2 : ℂ) • Matrix.single 1 1 1) : C = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single 1 1 1) := by
  have hformula (a : Fin 3) (e : Fin 2) :
      D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) e =
        (1/2 : ℂ) • (1 + ((-1 : ℂ) ^ e.val) • pauli a) := by
    exact Matrix.ext (fun i => congrFun rfl)
  have hplus (a : Fin 3) (e : Bool) : C ((fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) a e) = Matrix.single 1 1 1 := by
    have he : 1 - (fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) a e = (fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) a (!e) := by
      cases e <;> simp [hformula] <;> module
    rw [bounded_pure_output C hC hone _ (density_psd a e) (he.symm ▸ density_psd a (!e)), density_trace, one_smul]
  have hs (a : Fin 3) : C (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli a) = 0 := by
    have he : D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli a = (fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) a false - (fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) a true := by
      simp [hformula]; module
    rw [he, map_sub, hplus, hplus, sub_self]
  ext X i j
  nth_rw 1 [pauli_expansion X]
  simp only [hformula, map_add, map_sum, map_smul, hs, smul_zero, Finset.sum_const_zero, add_zero, hone]; fin_cases i <;> fin_cases j <;> simp [hformula, D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, smul_smul, Matrix.single] <;> ring

end QubitPure
open Qubit QubitUnital PauliChannels QubitPure
namespace QubitUnitalAction
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
private lemma coeff_bounds (B : MatrixMap (Fin 2) (Fin 2) ℂ) (hB : IsCPTP B) (hu : B 1 = 1) (a b : Fin 3) : -1 ≤ ((Matrix.trace (pauli a * B (pauli b))).re / 2) ∧ ((Matrix.trace (pauli a * B (pauli b))).re / 2) ≤ 1 ∧ Matrix.trace (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli a * B (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b)) / 2 = (((Matrix.trace (pauli a * B (pauli b))).re / 2) : ℂ) := by
  have hformula (a : Fin 3) (e : Fin 2) :
      D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) e =
        (1/2 : ℂ) • (1 + ((-1 : ℂ) ^ e.val) • pauli a) := by
    exact Matrix.ext (fun i => congrFun rfl)
  have ep : Matrix.trace ((fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) a false * B ((fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) b false)) = (1/2 : ℂ) + (1/4 : ℂ) * Matrix.trace (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli a * B (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b)) := by
    simp [hformula,  map_add, map_smul, hu, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, hB.2, sigma_trace, Matrix.trace_one, Fintype.card_fin]; ring
  have em : Matrix.trace ((fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) a true * B ((fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) b false)) = (1/2 : ℂ) - (1/4 : ℂ) * Matrix.trace (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli a * B (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b)) := by
    simp [hformula,  map_add, map_smul, hu, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, hB.2, sigma_trace, Matrix.trace_one, Fintype.card_fin]; ring
  have hp := Complex.nonneg_iff.mp ((density_psd a false).trace_mul_nonneg ((fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) hB (density_psd b false)))
  have hm := Complex.nonneg_iff.mp ((density_psd a true).trace_mul_nonneg ((fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) hB (density_psd b false))); rw [ep] at hp; rw [em] at hm; norm_num [Complex.mul_re, Complex.mul_im] at hp hm; refine ⟨?_, ?_, ?_⟩
  · linarith [hp.1]
  · linarith [hm.1]
  · apply Complex.ext
    · simp [hformula, div_eq_mul_inv, Complex.mul_re]
    · simp [hformula, div_eq_mul_inv, Complex.mul_im]
      linarith [hp.2]
private lemma channel_pauli_expansion (B : MatrixMap (Fin 2) (Fin 2) ℂ) (hB : IsCPTP B) (hu : B 1 = 1) (X : QubitMatrix) : B X = (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) X + ∑ a : Fin 3, ∑ b : Fin 3, (((Matrix.trace (pauli a * B (pauli b))).re / 2) : ℂ) • L a b X := by
  have hs (b : Fin 3) : B (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b) = ∑ a : Fin 3, (((Matrix.trace (pauli a * B (pauli b))).re / 2) : ℂ) • D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli a := by
    have he := pauli_expansion (B (D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli b)); rw [hB.2, sigma_trace, zero_div, zero_smul, zero_add] at he
    calc
      _ = ∑ a : Fin 3, (Matrix.trace (pauli a * B (pauli b)) / 2) • pauli a := he
      _ = _ := by
        apply Finset.sum_congr rfl; intro a ha
        exact congrArg (fun z : ℂ => z • pauli a) (coeff_bounds B hB hu a b).2.2
  nth_rw 1 [pauli_expansion X]
  simp only [map_add, map_sum, map_smul, hu]
  have hsum : (∑ b : Fin 3, (Matrix.trace (pauli b * X) / 2) • B (pauli b)) =
      ∑ b : Fin 3, (Matrix.trace (pauli b * X) / 2) •
        ∑ a : Fin 3, (((Matrix.trace (pauli a * B (pauli b))).re / 2) : ℂ) • pauli a := by
    apply Finset.sum_congr rfl; intro b hb
    exact congrArg (fun M => (Matrix.trace (pauli b * X) / 2) • M) (hs b)
  rw [hsum]
  simp only [Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]
  ext i j
  simp [ D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, L, Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
private def weight (B : MatrixMap (Fin 2) (Fin 2) ℂ) (x : Fin 3 × Fin 3 × Bool) : ℝ :=
  (1 + (if x.2.2 then -1 else 1) * ((Matrix.trace (pauli x.1 * B (pauli x.2.1))).re / 2)) / 18
private lemma weight_nonneg (B : MatrixMap (Fin 2) (Fin 2) ℂ) (hB : IsCPTP B) (hu : B 1 = 1) (x : Fin 3 × Fin 3 × Bool) : 0 ≤ weight B x := by
  have h := coeff_bounds B hB hu x.1 x.2.1
  rcases x with ⟨a,b,e⟩
  cases e <;> simp [weight] <;> linarith [h.1,h.2.1]
private lemma weight_sum (B : MatrixMap (Fin 2) (Fin 2) ℂ) : ∑ x, weight B x = 1 := by
  simp [Fintype.sum_prod_type, weight, Fintype.sum_bool, Fin.sum_univ_three]; ring
private lemma finite_pauli_identity (B : MatrixMap (Fin 2) (Fin 2) ℂ) (hB : IsCPTP B) (hu : B 1 = 1) : (1/9 : ℂ) • B + (8/9 : ℂ) • (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) = ∑ x : Fin 3 × Fin 3 × Bool, (weight B x : ℂ) • PauliChannels.D x.1 x.2.1 x.2.2 := by
  ext X i j
  rw [LinearMap.add_apply, LinearMap.smul_apply, channel_pauli_expansion B hB hu]; simp only [Fintype.sum_prod_type, Fintype.sum_bool, PauliChannels.D, weight]; simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]; push_cast; simp only [Bool.false_eq_true, ↓reduceIte, one_mul]; simp only [Fin.sum_univ_three]; ring
private lemma dual_pauli_formula (B : MatrixMap (Fin 2) (Fin 2) ℂ) (hB : IsCPTP B) (hu : B 1 = 1) :
    MatrixMap.dual B = D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2 +
      ∑ a : Fin 3, ∑ b : Fin 3, (((Matrix.trace (pauli a * B (pauli b))).re / 2) : ℂ) • L b a := by
  apply LinearMap.ext; intro X; apply Matrix.ext_iff_trace_mul_right.mpr; intro Y
  have ht := MatrixMap.Dual.trace_eq B Y X
  rw [Matrix.trace_mul_comm (B Y), Matrix.trace_mul_comm Y] at ht
  rw [← ht, channel_pauli_expansion B hB hu]
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, L, D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.add_mul, Matrix.mul_add, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, Matrix.mul_one, Matrix.one_mul, smul_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  simp_rw [Matrix.trace_mul_comm X]
  simp [LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
private lemma reversed_pauli_identity (B : MatrixMap (Fin 2) (Fin 2) ℂ) (hB : IsCPTP B) (hu : B 1 = 1) : (1/9 : ℂ) • MatrixMap.dual B + (8/9 : ℂ) • (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) = ∑ x : Fin 3 × Fin 3 × Bool, (weight B x : ℂ) • PauliChannels.D x.2.1 x.1 x.2.2 := by
  ext X i j
  rw [dual_pauli_formula B hB hu]; simp only [Fintype.sum_prod_type, Fintype.sum_bool, PauliChannels.D, weight]; simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]; push_cast; simp only [Bool.false_eq_true, ↓reduceIte, one_mul]; simp only [Fin.sum_univ_three]; ring
private lemma unital_reversed {S : MatrixMap (Fin 2) (Fin 2) ℂ → MatrixMap (Fin 2) (Fin 2) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) (B : MatrixMap (Fin 2) (Fin 2) ℂ) (hB : IsCPTP B) (hu : B 1 = 1) : S B = MatrixMap.dual B := by
  have he := finite_randomisation hS (Finset.univ : Finset (Fin 3 × Fin 3 × Bool)) (weight B) (fun x => PauliChannels.D x.1 x.2.1 x.2.2) (fun x hx => weight_nonneg B hB hu x) (by simpa using weight_sum B) (fun x hx => D_cptp x.1 x.2.1 x.2.2); rw [← finite_pauli_identity B hB hu] at he
  have hb := hS.2 B (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) hB Delta_cptp (1/9) (by norm_num) (by norm_num); norm_num at hb; rw [hb, Delta_fixed hS ht] at he; simp_rw [D_reversed hS ht] at he; rw [← reversed_pauli_identity B hB hu] at he
  ext X i j
  have hx := congrArg (fun F => F X i j) he; simp only [LinearMap.add_apply, LinearMap.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hx; linear_combination 9 * hx
private lemma adjoint_unital (B : MatrixMap (Fin 2) (Fin 2) ℂ) (hB : IsCPTP B) : MatrixMap.dual B 1 = 1 := by
  apply Matrix.ext_iff_trace_mul_left.mpr; intro Y
  have h := MatrixMap.Dual.trace_eq B Y 1
  simpa only [Matrix.mul_one, hB.2] using h.symm
private lemma adjoint_trace (B : MatrixMap (Fin 2) (Fin 2) ℂ) (hB : IsCPTP B) (hu : B 1 = 1) (X Y : QubitMatrix) : Matrix.trace (MatrixMap.dual B X * Y) = Matrix.trace (X * B Y) := by
  rw [Matrix.trace_mul_comm (MatrixMap.dual B X) Y, ← MatrixMap.Dual.trace_eq B Y X, Matrix.trace_mul_comm (B Y) X]
private lemma adjoint_eq_delta (B : MatrixMap (Fin 2) (Fin 2) ℂ) (hB : IsCPTP B) (hu : B 1 = 1) (he : MatrixMap.dual B = (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2)) : B = (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) := by
  apply LinearMap.ext; intro X; apply Matrix.ext_iff_trace_mul_left.mpr; intro Y
  have ht := adjoint_trace B hB hu Y X
  rw [he] at ht
  simpa [D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_smul, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using ht.symm
end QubitUnitalAction
open Qubit QubitUnital PauliChannels QubitPure QubitUnitalAction
namespace QubitPreimage
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
private lemma preimage_replacement {S : MatrixMap (Fin 2) (Fin 2) ℂ → MatrixMap (Fin 2) (Fin 2) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) (Phi : MatrixMap (Fin 2) (Fin 2) ℂ) (hPhi : IsCPTP Phi) (hp : S Phi = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single 0 0 1)) : Phi = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) ((1/2 : ℂ) • Phi 1) := by
  let F := J ∘ₗ Phi ∘ₗ J
  let B := (1/2 : ℂ) • (Phi + F)
  have hF : IsCPTP F := spinflip_cptp Phi hPhi
  have hB : IsCPTP B := by
    convert cptp_mix (p := (1/2:ℝ)) hPhi hF (by norm_num) (by norm_num) using 1
    norm_num; module
  have hBu : B 1 = 1 := unitalisation_unital Phi hPhi
  have hSB := unital_reversed hS ht B hB hBu
  have hmid : S B = (1/2 : ℂ) • (((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single 0 0 1) + S F) := by
    have hm := hS.2 Phi F hPhi hF (1/2) (by norm_num) (by norm_num); norm_num at hm
    have hd : B = (1/2:ℂ) • Phi + (1/2:ℂ) • F := by exact smul_add _ _ _
    rw [hd,hm,hp]; module
  have hCone : S F 1 = (2 : ℂ) • Matrix.single 1 1 1 := by
    have hi := congrArg (fun M => M (1 : QubitMatrix)) hmid; rw [hSB, adjoint_unital B hB] at hi
    ext i j
    have hj := congrArg (fun X : QubitMatrix => X i j) hi; fin_cases i <;> fin_cases j <;> simp [D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.trace_one, Fintype.card_fin, Matrix.single] at hj ⊢ <;> first | exact hj | linear_combination -2 * hj
  have hC := pure_output_replacement (S F) (hS.1.1 hF) hCone
  have hsDelta : S B = (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) := by
    rw [hmid,hC]
    ext X i j
    fin_cases i <;> fin_cases j <;> simp [D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply,  Matrix.single, Matrix.trace, Matrix.diag, Fin.sum_univ_two] <;> ring
  have hbDelta : B = (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) := adjoint_eq_delta B hB hBu (hSB.symm.trans hsDelta)
  have hm := unitalisation_midpoint Phi hPhi; change B = _ at hm; rw [hbDelta] at hm
  ext X i j
  have hej := congrArg (fun M => M X i j) hm; simp only [LinearMap.add_apply, LinearMap.sub_apply, Matrix.add_apply, Matrix.sub_apply] at hej; linear_combination -hej
private lemma determinant_bounds (rho : QubitMatrix) (hρ : rho.PosSemidef) (htr : Matrix.trace rho = 1) : 0 ≤ (Matrix.det rho).re ∧ (Matrix.det rho).re ≤ 1/4 ∧ (Matrix.det rho).im = 0 := by
  have hd := D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.qubit_det_bounds rho hρ htr
  exact ⟨hd.1, hd.2, (Complex.nonneg_iff.mp hρ.det_nonneg).2.symm⟩
private lemma density_determinant_mixture (rho : QubitMatrix) (hρ : rho.PosSemidef) (htr : Matrix.trace rho = 1) : ∃ eta : QubitMatrix, eta.PosSemidef ∧ Matrix.trace eta = 1 ∧ ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) rho = ((1-2*(Matrix.det rho).re : ℝ) : ℂ) • ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) eta + ((2*(Matrix.det rho).re : ℝ) : ℂ) • (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) := by
  let δ := (Matrix.det rho).re
  let μ := 1-2*δ
  have hd := determinant_bounds rho hρ htr
  have hμ : 0 < μ := by dsimp [μ,δ]; linarith [hd.2.1]
  have hδ : Matrix.det rho = (δ : ℂ) := by
    apply Complex.ext <;> simp [δ, hd.2.2]
  have hμz : (μ : ℂ) ≠ 0 := by exact Complex.ne_zero_of_re_pos hμ
  let eta : QubitMatrix := ((μ⁻¹ : ℝ) : ℂ) • (rho * rho)
  have hepsd : eta.PosSemidef := by
    change (μ⁻¹ • (rho * rho)).PosSemidef
    have hsqpsd : (rho * rho).PosSemidef := by simpa [pow_two] using hρ.pow 2
    exact hsqpsd.smul (inv_nonneg.mpr (le_of_lt hμ))
  have hch := density_cayley_hamilton rho htr; rw [hδ] at hch
  have htrsq : Matrix.trace (rho * rho) = (μ : ℂ) := by
    have hh := congrArg Matrix.trace hch; simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_zero, Matrix.trace_one, Fintype.card_fin, htr, smul_eq_mul] at hh; dsimp [μ]; push_cast; linear_combination hh
  have het : Matrix.trace eta = 1 := by
    simp only [eta, Matrix.trace_smul, htrsq, smul_eq_mul, Complex.ofReal_inv]; exact inv_mul_cancel₀ hμz
  refine ⟨eta,hepsd,het,?_⟩
  have hm : (μ : ℂ) • eta = rho * rho := by
    simp [eta, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hμ)]
  have he : rho = (μ : ℂ) • eta + (δ : ℂ) • 1 := by
    rw [hm]
    ext i j
    have hh := congrArg (fun M : QubitMatrix => M i j) hch; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hh ⊢; linear_combination -hh
  have htwo : ((2*δ : ℝ) : ℂ) = 2*(δ : ℂ) := by push_cast; rfl
  change ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) rho = (μ : ℂ) • ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) eta + ((2*δ : ℝ) : ℂ) • (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2); rw [htwo]
  ext X i j
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hej := congrArg (fun M : QubitMatrix => M i j) he; simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at hej; linear_combination Matrix.trace X * hej
private lemma pure_preimage {S : MatrixMap (Fin 2) (Fin 2) ℂ → MatrixMap (Fin 2) (Fin 2) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) (Phi : MatrixMap (Fin 2) (Fin 2) ℂ) (hPhi : IsCPTP Phi) (hp : S Phi = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single 0 0 1)) : ∃ rho : QubitMatrix, rho.PosSemidef ∧ Matrix.trace rho = 1 ∧ Matrix.det rho = 0 ∧ Phi = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) rho ∧ S (((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) rho) = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single 0 0 1) := by
  let rho := (1/2 : ℂ) • Phi 1
  have hρ : rho.PosSemidef := by
    exact ((fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) hPhi Matrix.PosSemidef.one).smul (show (0:ℂ) ≤ 1/2 by norm_num [Complex.nonneg_iff])
  have htr : Matrix.trace rho = 1 := by
    simp [rho, Matrix.trace_smul, hPhi.2, Matrix.trace_one, Fintype.card_fin]
  have hrep : Phi = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) rho := preimage_replacement hS ht Phi hPhi hp
  have hsrep : S (((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) rho) = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single 0 0 1) := by rw [← hrep]; exact hp
  obtain ⟨eta,hepsd,het,hmix⟩ := density_determinant_mixture rho hρ htr
  have hd := determinant_bounds rho hρ htr
  have heta := replacement_cptp eta hepsd het
  let δ := (Matrix.det rho).re
  have hmu0 : 0 ≤ 1-2*δ := by dsimp [δ]; linarith [hd.2.1]
  have hmu1 : 1-2*δ ≤ 1 := by dsimp [δ]; linarith [hd.1]
  have he := hS.2 (((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) eta) (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) heta Delta_cptp (1-2*δ) hmu0 hmu1
  have hcoef : ((1-(1-2*δ) : ℝ) : ℂ) = ((2*δ : ℝ) : ℂ) := by congr 1; ring
  rw [hcoef, ← hmix, hsrep, Delta_fixed hS ht] at he
  have e00psd : (Matrix.single (0:Fin 2) 0 (1:ℂ)).PosSemidef := by
    exact D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree.unit_psd 0
  have hn := (Complex.nonneg_iff.mp (((fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) (hS.1.1 heta) e00psd).diag_nonneg (i := 1))).1
  have hx := congrArg (fun F => (F (Matrix.single (0:Fin 2) 0 1) 1 1).re) he; simp [D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply,  Matrix.single, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Complex.mul_re, Complex.ofReal_im] at hx hn
  have hδ0 : 0 ≤ δ := hd.1
  have hz : δ = 0 := by nlinarith [mul_nonneg hmu0 hn, hδ0]
  have hdet : Matrix.det rho = 0 := by
    apply Complex.ext
    · exact hz
    · simpa using hd.2.2
  exact ⟨rho,hρ,htr,hdet,hrep,hsrep⟩
end QubitPreimage
open Qubit QubitUnital PauliChannels QubitPure QubitUnitalAction QubitPreimage
namespace QubitRotation
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
private lemma pure_density_rotation (rho : QubitMatrix) (hρ : rho.PosSemidef) (htr : Matrix.trace rho = 1) (hdet : Matrix.det rho = 0) : ∃ W : QubitMatrix, W ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ unitaryChannel W (Matrix.single 0 0 1) = rho := by
  let a := (rho 0 0).re
  let b := rho 0 1
  have had := Complex.nonneg_iff.mp (hρ.diag_nonneg (i := 0))
  have ha : rho 0 0 = (a : ℂ) := by exact Complex.eq_re_of_ofReal_le had
  have h10 : rho 1 0 = (starRingEnd ℂ) b := (hρ.isHermitian.apply 1 0).symm
  have h11 : rho 1 1 = 1-(a : ℂ) := by
    have ht : rho 0 0 + rho 1 1 = 1 := by simpa [Matrix.trace,Matrix.diag,Fin.sum_univ_two] using htr
    rw [ha] at ht; linear_combination ht
  have hab : (starRingEnd ℂ) b * b = (a : ℂ) * (1-(a : ℂ)) := by
    simp only [unitaryChannel, Matrix.det_fin_two, ha, h11, h10] at hdet; change (a:ℂ)*(1-(a:ℂ))-b*(starRingEnd ℂ) b=0 at hdet; linear_combination -hdet
  have hab' : b * (starRingEnd ℂ) b = (a : ℂ) * (1-(a : ℂ)) := by rw [mul_comm]; exact hab
  by_cases haz : a = 0
  · have hzero : rho 0 0 = 0 := by rw [ha,haz]; rfl
    have hr : rho = Matrix.single 1 1 1 := by simpa [htr] using psd_zero_corner rho hρ hzero
    refine ⟨D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli 0,sigma_unitary 0,?_⟩; rw [hr]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unitaryChannel, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli,pauliMatrix,qubitX,qubitZ,Matrix.single, Matrix.mul_apply,Matrix.vecMul,Matrix.vecHead,Matrix.vecTail,dotProduct,Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose,Fin.sum_univ_two]
  · have hap : 0 < a := lt_of_le_of_ne had.1 (Ne.symm haz)
    let s : ℂ := ((Real.sqrt a : ℝ) : ℂ)
    have hs : s^2 = (a : ℂ) := by dsimp [s]; exact_mod_cast Real.sq_sqrt (le_of_lt hap)
    have hs0 : s ≠ 0 := by dsimp [s]; exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hap)
    have hss : (starRingEnd ℂ) s = s := by exact Complex.conj_ofReal _
    let W : QubitMatrix := !![s,-b/s;(starRingEnd ℂ) b/s,s]
    have hWu : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
      apply Matrix.mem_unitaryGroup_iff'.mpr
      ext i j
      fin_cases i <;> fin_cases j <;> simp [unitaryChannel, W,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.star_eq_conjTranspose, Fin.sum_univ_two,Complex.star_def,hss] <;> field_simp [hs0] <;> try ring
      all_goals
        linear_combination (s^2+(a:ℂ)-1) * hs + hab
    refine ⟨W,hWu,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unitaryChannel, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,W,Matrix.mul_apply,Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose,Fin.sum_univ_two,Matrix.single,Matrix.vecHead,Matrix.vecTail,Complex.star_def,hss, ha,h10,h11] <;> field_simp [hs0] <;> try ring
    all_goals first | exact hs | linear_combination (1-(a:ℂ)) * hs - hab | linear_combination hab - (1-(a:ℂ)) * hs
end QubitRotation
open Qubit QubitUnital PauliChannels QubitPure QubitUnitalAction QubitPreimage QubitRotation
namespace QubitWitness
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
private lemma cptp_comp (F G : MatrixMap (Fin 2) (Fin 2) ℂ) (hF : IsCPTP F) (hG : IsCPTP G) : IsCPTP (F ∘ₗ G) := by
  refine ⟨D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.cp_comp hF.1 hG.1,?_⟩; intro X; simp only [LinearMap.comp_apply,hF.2,hG.2]
private lemma unitary_unital (W : QubitMatrix) (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) : unitaryChannel W 1 = 1 := by
  change W * 1 * star W = 1; rw [Matrix.mul_one]; exact Matrix.mem_unitaryGroup_iff.mp hW
private lemma unitary_delta (W V : QubitMatrix) (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) : unitaryChannel W ∘ₗ (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) ∘ₗ unitaryChannel V = (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2)  := by
  apply LinearMap.ext
  intro X
  change unitaryChannel W ((Matrix.trace (unitaryChannel V X) / 2) • (1:QubitMatrix)) = (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) X
  rw [(unitaryChannel_cptp hV).2, map_smul, unitary_unital W hW]
  rfl
private lemma H_unitary : (PauliChannels.W 0 2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := G_unitary 0 2 false
private lemma H_star : star (PauliChannels.W 0 2) = (PauliChannels.W 0 2) := by
  simp [PauliChannels.W,star_add,star_smul,sigma_star]
private lemma u4_unitary (j : Fin 4) : D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma j ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  fin_cases j
  · exact (Matrix.unitaryGroup _ _).one_mem
  · exact sigma_unitary 0
  · exact sigma_unitary 1
  · exact sigma_unitary 2
private lemma u4_star (j : Fin 4) : star (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma j) = D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma j  := by
  fin_cases j <;> simp [D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma, Matrix.star_eq_conjTranspose, D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian]
private lemma p4_nonneg (j : Fin 4) : 0 ≤ p4 j := by fin_cases j <;> norm_num [p4]
private lemma p4_sum : ∑ j, p4 j = 1 := by norm_num [p4,Fin.sum_univ_succ]
private lemma B0_mixture : (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel p4) = ∑ j : Fin 4, (p4 j : ℂ) • unitaryChannel (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma j)  := by
  ext X i j
  simp [unitaryChannel, p4, D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel, D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma, p4, Fin.sum_univ_succ, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, Matrix.star_eq_conjTranspose, D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian, add_assoc]
private lemma B0_cptp : IsCPTP (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel p4) := by
  exact D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.channel_cptp p4 p4_nonneg p4_sum
private lemma conjugated_mixture (W V : QubitMatrix) : unitaryChannel W ∘ₗ (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel p4) ∘ₗ unitaryChannel V = ∑ j : Fin 4, (p4 j : ℂ) • unitaryChannel ((W*D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma j)*V) := by
  rw [B0_mixture]
  ext X i j
  simp [Part1Finite.unitary_comp,LinearMap.comp_apply,map_sum,map_smul, Matrix.mul_assoc]
private lemma conjugated_reverse {S : MatrixMap (Fin 2) (Fin 2) ℂ → MatrixMap (Fin 2) (Fin 2) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) (W : QubitMatrix) (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) : S (unitaryChannel W ∘ₗ (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel p4) ∘ₗ unitaryChannel (PauliChannels.W 0 2)) = unitaryChannel (PauliChannels.W 0 2) ∘ₗ (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel p4) ∘ₗ unitaryChannel (star W) := by
  rw [conjugated_mixture]
  have h := finite_randomisation hS (Finset.univ : Finset (Fin 4)) p4 (fun j => unitaryChannel ((W*D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma j)*(PauliChannels.W 0 2))) (fun j hj => p4_nonneg j) (by simpa using p4_sum) (by
      intro j hj; exact unitaryChannel_cptp ((Matrix.unitaryGroup _ _).mul_mem ((Matrix.unitaryGroup _ _).mul_mem hW (u4_unitary j)) H_unitary))
  rw [h,conjugated_mixture]; apply Finset.sum_congr rfl; intro j hj; rw [ht _ ((Matrix.unitaryGroup _ _).mul_mem ((Matrix.unitaryGroup _ _).mul_mem hW (u4_unitary j)) H_unitary),star_mul,star_mul, H_star,u4_star]; simp [Matrix.mul_assoc]
private lemma conjugated_amplitude_identity (W : QubitMatrix) (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) : (4/7:ℂ) • (unitaryChannel W ∘ₗ A0 ∘ₗ unitaryChannel (PauliChannels.W 0 2)) + (3/7:ℂ) • (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) = (4/7:ℂ) • (unitaryChannel W ∘ₗ (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel p4) ∘ₗ unitaryChannel (PauliChannels.W 0 2)) + (3/7:ℂ) • ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (unitaryChannel W (Matrix.single 0 0 1)) := by
  have hd := unitary_delta W (PauliChannels.W 0 2) hW H_unitary
  ext X i j
  have he := congrArg (fun F => unitaryChannel W (F (unitaryChannel (PauliChannels.W 0 2) X)) i j) amplitude_damping_identity; simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply, map_add,map_smul,map_sub] at he
  have hdr := congrArg (fun F => F X i j) hd; simp only [LinearMap.comp_apply] at hdr
  have hrep : unitaryChannel W (((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single 0 0 1) (unitaryChannel (PauliChannels.W 0 2) X)) = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (unitaryChannel W (Matrix.single 0 0 1)) X := by
    simp only [LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, map_smul, (unitaryChannel_cptp H_unitary).2]
  rw [hrep] at he; simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul] at he; rw [hdr] at he; simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.comp_apply, Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at he ⊢; linear_combination (4/7:ℂ) * he
private lemma fixed_witness_output : unitaryChannel (PauliChannels.W 0 2) ((D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel p4) ((fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) 0 false)) = !![3/4,0;0,1/4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitaryChannel, D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral, PauliChannels.W,p4, D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel, D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma, Fin.sum_univ_succ, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.diag, Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose,Pi.star_apply,map_inv₀,map_ofNat, Fin.sum_univ_two,Complex.I_mul_I] <;> try ring_nf <;> norm_num [r_square,Complex.I_sq,Complex.I_pow_three] <;> try ring
  all_goals norm_num only [r_square] <;> ring

end QubitWitness
open Qubit QubitUnital PauliChannels QubitPure QubitUnitalAction QubitPreimage QubitRotation QubitWitness
namespace QubitNoGo
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
private lemma forced_witness_output {S : MatrixMap (Fin 2) (Fin 2) ℂ → MatrixMap (Fin 2) (Fin 2) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) (W : QubitMatrix) (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hp : S (((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (unitaryChannel W (Matrix.single 0 0 1))) = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single 0 0 1)) : S (unitaryChannel W ∘ₗ A0 ∘ₗ unitaryChannel (PauliChannels.W 0 2)) (unitaryChannel W ((fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) 0 false)) = !![9/8,0;0,-1/8] := by
  let A := unitaryChannel W ∘ₗ A0 ∘ₗ unitaryChannel (PauliChannels.W 0 2)
  let B := unitaryChannel W ∘ₗ (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel p4) ∘ₗ unitaryChannel (PauliChannels.W 0 2)
  let R := ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (unitaryChannel W (Matrix.single 0 0 1))
  let omega : QubitMatrix := unitaryChannel W ((fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) 0 false)
  have hu := unitaryChannel_cptp hW
  have hh := unitaryChannel_cptp QubitWitness.H_unitary
  have hA : IsCPTP A := cptp_comp _ _ hu (cptp_comp _ _ A0_cptp hh)
  have hB : IsCPTP B := cptp_comp _ _ hu (cptp_comp _ _ B0_cptp hh)
  have he00 : (Matrix.single (0:Fin 2) 0 (1:ℂ)).PosSemidef := by
    exact D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree.unit_psd 0
  have hR : IsCPTP R := replacement_cptp _ ((fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) hu he00) (by
    rw [hu.2]; simp [Matrix.trace,Matrix.diag,Matrix.single])
  have h23 := congrArg S (conjugated_amplitude_identity W hW)
  have hAS := hS.2 A (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) hA Delta_cptp (4/7) (by norm_num) (by norm_num)
  have hBR := hS.2 B R hB hR (4/7) (by norm_num) (by norm_num); norm_num at hAS hBR; change S ((4/7:ℂ) • A + (3/7:ℂ) • (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2)) = S ((4/7:ℂ) • B + (3/7:ℂ) • R) at h23; rw [hAS,hBR,Delta_fixed hS ht,conjugated_reverse hS ht W hW,hp] at h23
  have htr : Matrix.trace omega = 1 := by rw [hu.2]; exact density_trace 0 false
  have hback : unitaryChannel (star W) omega = (fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) 0 false := by
    change star W * (W * (fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) 0 false * star W) * star (star W) = (fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) 0 false; rw [star_star]
    calc
      _ = (star W * W) * (fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) 0 false * (star W * W) := by simp only [Matrix.mul_assoc]
      _ = (fun (a : Fin 3) (e : Bool) => D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (![Pauli.X, Pauli.Y, Pauli.Z] a) (if e then 1 else 0)) 0 false := by rw [Matrix.mem_unitaryGroup_iff'.mp hW]; simp
  have hBomega : (unitaryChannel (PauliChannels.W 0 2) ∘ₗ (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.pauliChannel p4) ∘ₗ unitaryChannel (star W)) omega = !![3/4,0;0,1/4] := by
    simp only [LinearMap.comp_apply,hback]; exact fixed_witness_output
  have hDomega : (D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol 2) omega = (1/2:ℂ) • (1 : QubitMatrix) := by simp [D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply,htr]
  have hRomega : ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single (0:Fin 2) 0 (1:ℂ)) omega = Matrix.single (0:Fin 2) 0 (1:ℂ) := by
    simp [D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply,htr]
  have hout := congrArg (fun F => F omega) h23; simp only [LinearMap.add_apply,LinearMap.smul_apply,hBomega,hDomega,hRomega] at hout; change S A omega = _
  ext i j
  have hej := congrArg (fun M : QubitMatrix => M i j) hout; fin_cases i <;> fin_cases j <;> simp [Matrix.single,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,htr] at hej ⊢ <;> first | exact hej | linear_combination (7/4:ℂ) * hej
private theorem inverse_unitary_no_go {S : MatrixMap (Fin 2) (Fin 2) ℂ → MatrixMap (Fin 2) (Fin 2) ℂ} (hS : IsChannelSymmetry S) (ht : ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, S (unitaryChannel U) = unitaryChannel (star U)) : False := by
  have he00 : (Matrix.single (0:Fin 2) 0 (1:ℂ)).PosSemidef := by
    exact D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree.unit_psd 0
  have hR0 := replacement_cptp _ he00 (by simp [Matrix.trace,Matrix.diag,Matrix.single])
  obtain ⟨Phi,hPhi,hp⟩ := hS.1.2.2 hR0
  obtain ⟨rho,hρ,htr,hdet,hrep,hsrep⟩ := pure_preimage hS ht Phi hPhi hp
  obtain ⟨W,hW,hw⟩ := pure_density_rotation rho hρ htr hdet
  have hpW : S (((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (unitaryChannel W (Matrix.single 0 0 1))) = ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight) (Matrix.single 0 0 1) := by rw [hw]; exact hsrep
  have he := forced_witness_output hS ht W hW hpW
  have hu := unitaryChannel_cptp hW
  have hh := unitaryChannel_cptp QubitWitness.H_unitary
  have hA := cptp_comp _ _ hu (cptp_comp _ _ A0_cptp hh)
  have hn := (fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) (hS.1.1 hA) ((fun {d : ℕ} {Phi : MatrixMap (Fin d) (Fin d) ℂ} (hPhi : IsCPTP Phi) {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) => hPhi.1.IsPositive hX) hu (density_psd 0 false)); rw [he] at hn
  have hbad := Complex.nonneg_iff.mp (hn.diag_nonneg (i := 1)); norm_num at hbad
end QubitNoGo
theorem result : claim := by
  intro d hd S hS
  have hstar : ¬ ∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, S (unitaryChannel U) = unitaryChannel (star U) := by
    intro ht
    by_cases hd2 : d = 2
    · subst d
      exact QubitNoGo.inverse_unitary_no_go hS ht
    · have hd3 : 3 ≤ d := by omega
      obtain ⟨n,rfl⟩ : ∃ n, d = n+3 := ⟨d-3,by omega⟩
      exact Part1NoGo.inverse_unitary_no_go n hS ht
  refine ⟨hstar,?_⟩; intro ht
  obtain ⟨hk,hkt⟩ := transpose_target_reduces_to_star hS ht
  by_cases hd2 : d = 2
  · subst d
    exact QubitNoGo.inverse_unitary_no_go hk hkt
  · have hd3 : 3 ≤ d := by omega
    obtain ⟨n,rfl⟩ : ∃ n, d = n+3 := ⟨d-3,by omega⟩
    exact Part1NoGo.inverse_unitary_no_go n hk hkt
end D5.S3.QuantumChannels.ChannelTimeReversalNoGo
