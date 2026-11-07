/- GID: D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Scalar line-preserving obstructions classify linear versus square-root infidelity. -/

/-
admission_basis: open-problem-resolution (#24695; Proved).
unitInputFamily: proof_shape: bind-only; escape_witness: none; consumers: channel_gram_defect,claim,completed_obstruction,general_channel_upper,identity_admissible,nonscalar_implies_sqrt,nonscalar_sqrt_lower,normalized_obstruction,obstruction_sub_scalar,reset_admissible,result,scalar_channel_upper,scalar_implies_linear,traceless_obstruction,universal_linear_lower.
spanInputFamily: proof_shape: bind-only; escape_witness: none; consumers: claim,eq_1,general_channel_upper,nonscalar_implies_sqrt,result.
nonorthogonalityConnected: proof_shape: bind-only; escape_witness: none; consumers: claim,general_channel_upper,nonscalar_implies_sqrt,result.
survivalFidelity: proof_shape: bind-only; escape_witness: none; consumers: admissibleAt,channel_gram_defect,envVector_norm_sq,fidelity_bddBelow,general_channel_upper,identity_admissible,kraus_input_loss,kraus_survival,nonscalar_sqrt_lower,reset_admissible,residualVector_norm_sq,scalar_channel_upper.
admissibleAt: proof_shape: bind-only; escape_witness: none; consumers: f,f_lower_of_channel,f_upper_of_channels,fidelity_bddBelow,general_channel_upper,identity_admissible,nonscalar_implies_sqrt,nonscalar_sqrt_lower,reset_admissible,scalar_channel_upper,scalar_implies_linear.
f: proof_shape: bind-only; escape_witness: none; consumers: LinearScaling,SqrtScaling,f_lower_of_channel,f_upper_of_channels,nonscalar_implies_sqrt,nonscalar_sqrt_lower,scalar_implies_linear,scaling_exclusive,universal_linear_lower.
obstructionSpace: proof_shape: bind-only; escape_witness: none; consumers: completed_obstruction,nonscalar_sqrt_lower,normalized_obstruction,obstruction_sub_scalar,scalarObstruction,scalar_detection_injective,traceless_obstruction.
scalarObstruction: proof_shape: bind-only; escape_witness: none; consumers: claim,completed_obstruction,nonscalar_implies_sqrt,nonscalar_sqrt_lower,normalized_obstruction,result,scalar_channel_upper,scalar_coercivity,scalar_coercivity_sq,scalar_detection_injective,scalar_implies_linear,traceless_obstruction.
LinearScaling: proof_shape: bind-only; escape_witness: none; consumers: claim,result,scalar_implies_linear,scaling_exclusive.
SqrtScaling: proof_shape: bind-only; escape_witness: none; consumers: claim,nonscalar_implies_sqrt,result,scaling_exclusive.
claim: proof_shape: bind-only; escape_witness: none; consumers: result.
residual_iff: proof_shape: bind-only; escape_witness: none; consumers: residual_self.
residual_self: proof_shape: bind-only; escape_witness: none; consumers: completed_obstruction,obstruction_sub_scalar,scalar_channel_upper.
obstruction_sub_scalar: proof_shape: bind-only; escape_witness: none; consumers: traceless_obstruction.
traceless_obstruction: proof_shape: bind-only; escape_witness: none; consumers: normalized_obstruction.
normalized_obstruction: proof_shape: bind-only; escape_witness: none; consumers: completed_obstruction.
detectionMap: proof_shape: bind-only; escape_witness: none; consumers: eq_1,scalar_coercivity,scalar_detection_injective.
scalar_detection_injective: proof_shape: bind-only; escape_witness: none; consumers: scalar_coercivity.
scalar_coercivity: proof_shape: bind-only; escape_witness: none; consumers: scalar_coercivity_sq.
scalar_coercivity_sq: proof_shape: bind-only; escape_witness: none; consumers: scalar_channel_upper.
entangled_coordinates: proof_shape: bind-only; escape_witness: none; consumers: process_nonneg,process_trace.
process_nonneg: proof_shape: bind-only; escape_witness: none; consumers: fidelity_bddBelow.
fidelity_bddBelow: proof_shape: bind-only; escape_witness: none; consumers: f_lower_of_channel.
f_lower_of_channel: proof_shape: bind-only; escape_witness: none; consumers: nonscalar_sqrt_lower,universal_linear_lower.
f_upper_of_channels: proof_shape: bind-only; escape_witness: none; consumers: nonscalar_implies_sqrt,scalar_implies_linear.
scaling_exclusive: proof_shape: bind-only; escape_witness: none; consumers: result.
kraus_survival: proof_shape: bind-only; escape_witness: none; consumers: envVector_norm_sq,kraus_input_loss,reset_admissible.
entangled_amplitude: proof_shape: bind-only; escape_witness: none; consumers: process_trace.
choi_overlap: proof_shape: bind-only; escape_witness: none; consumers: process_trace.
process_trace: proof_shape: bind-only; escape_witness: none; consumers: kraus_process_loss,reset_process.
kraus_cptp: proof_shape: bind-only; escape_witness: none; consumers: identity_admissible,nonscalar_sqrt_lower,reset_admissible.
identity_kraus: proof_shape: bind-only; escape_witness: none; consumers: identity_admissible.
identity_admissible: proof_shape: bind-only; escape_witness: none; consumers: nonscalar_implies_sqrt,scalar_implies_linear.
centered_gram_trace: proof_shape: bind-only; escape_witness: none; consumers: centered_frobenius_sq.
centered_frobenius_sq: proof_shape: bind-only; escape_witness: none; consumers: centered_minimum,kraus_process_loss.
kraus_process_loss: proof_shape: bind-only; escape_witness: none; consumers: general_channel_upper,nonscalar_sqrt_lower,scalar_channel_upper.
kraus_input_loss: proof_shape: bind-only; escape_witness: none; consumers: nonscalar_sqrt_lower,residualVector_norm_sq,scalar_channel_upper.
contraction_gram_le: proof_shape: bind-only; escape_witness: none; consumers: sqrt_completion,sqrt_completion_distance.
sqrt_completion: proof_shape: bind-only; escape_witness: none; consumers: completed_obstruction.
sqrt_completion_distance: proof_shape: bind-only; escape_witness: none; consumers: completed_obstruction,completion_tested_residual.
residual_contraction: proof_shape: bind-only; escape_witness: none; consumers: completion_tested_residual.
completion_tested_residual: proof_shape: bind-only; escape_witness: none; consumers: completed_obstruction.
pair_distance_of_gram_defect: proof_shape: bind-only; escape_witness: none; consumers: overlap_distance_bound.
overlap_distance_bound: proof_shape: bind-only; escape_witness: none; consumers: general_channel_upper.
gram_defect_from_residuals: proof_shape: bind-only; escape_witness: none; consumers: channel_gram_defect.
evaluationMap: proof_shape: bind-only; escape_witness: none; consumers: eq_1,evaluation_injective,general_channel_upper,spanning_evaluation_coercivity.
evaluation_injective: proof_shape: bind-only; escape_witness: none; consumers: spanning_evaluation_coercivity.
spanning_evaluation_coercivity: proof_shape: bind-only; escape_witness: none; consumers: general_channel_upper.
completed_obstruction: proof_shape: bind-only; escape_witness: none; consumers: nonscalar_sqrt_lower.
sqrt_smul_gram: proof_shape: bind-only; escape_witness: none; consumers: reset_complete.
reset_complete: proof_shape: bind-only; escape_witness: none; consumers: reset_admissible.
reset_admissible: proof_shape: bind-only; escape_witness: none; consumers: universal_linear_lower.
reset_process: proof_shape: bind-only; escape_witness: none; consumers: universal_linear_lower.
universal_linear_lower: proof_shape: bind-only; escape_witness: none; consumers: scalar_implies_linear.
finite_kraus_of_cptp: proof_shape: bind-only; escape_witness: none; consumers: general_channel_upper,scalar_channel_upper.
scalar_channel_upper: proof_shape: bind-only; escape_witness: none; consumers: scalar_implies_linear.
scalar_implies_linear: proof_shape: bind-only; escape_witness: none; consumers: result.
nonscalar_sqrt_lower: proof_shape: bind-only; escape_witness: none; consumers: nonscalar_implies_sqrt.
envVector: proof_shape: bind-only; escape_witness: none; consumers: channel_gram_defect,envVector_norm_sq,eq_1,general_channel_upper,stinespring_decomposition.
residualVector: proof_shape: bind-only; escape_witness: none; consumers: channel_gram_defect,eq_1,general_channel_upper,residualVector_norm_sq,stinespring_decomposition.
envTensor_inner: proof_shape: bind-only; escape_witness: none; consumers: channel_gram_defect,envTensor_norm_sq.
envTensor_norm_sq: proof_shape: bind-only; escape_witness: none; consumers: channel_gram_defect,general_channel_upper.
stinespring_decomposition: proof_shape: bind-only; escape_witness: none; consumers: channel_gram_defect.
envVector_norm_sq: proof_shape: bind-only; escape_witness: none; consumers: channel_gram_defect.
residualVector_norm_sq: proof_shape: bind-only; escape_witness: none; consumers: channel_gram_defect,general_channel_upper.
channel_gram_defect: proof_shape: bind-only; escape_witness: none; consumers: general_channel_upper.
centered_minimum: proof_shape: bind-only; escape_witness: none; consumers: general_channel_upper.
general_channel_upper: proof_shape: content; escape_witness: D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingCore.finite_graph_squared_distance_bound; consumers: nonscalar_implies_sqrt.
nonscalar_implies_sqrt: proof_shape: content; escape_witness: general_channel_upper; consumers: result.
result: proof_shape: content; escape_witness: general_channel_upper; consumers: none.
Direct frozen dependencies (declaration statement_id):
D5/S3/Quantum/Foundation/FiniteKrausChannel: D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7; D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive sha256:31bd68fc3c839750d1a8ac1474555b08fcd9579b1627c81db36a58f3172e1252; D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsTracePreserving.of_kraus_isTracePreserving sha256:523ad634bd9aa701ba267fb6bebc693c5ff621948138657ad3742fde53662b7f; D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287; D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_1 sha256:5dc7bcde8ce2ae710c058683e5324d31e0ca70317f167566967eee1cf3b23bbb; D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_2 sha256:9b70ce4858eb731b17facafe93b167007eb9ca6533c641dc770fc553d31ddaa1; D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f.
D5/S3/Quantum/GNSMatrix: D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace sha256:470140292aee89705512206af514f5a42fdc3948e5c9195d302613a47b859917.
D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral: D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockSpectral.rankOneQuadratic sha256:5659aa687c061edd25e159ca3e5a9a61692535f1343999094decbbcde1c7500a.
D5/S3/Quantum/PureState/PureStateHandshake: D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake sha256:3f3685dfb0637d23f5f799f8ec2e875fbc8fee9823e2940f31ba7983a7b83b1e; D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3; D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity.eq_1 sha256:55ceee4e54981d736399b2ba2deac31b5133affdd52e4a1aec12c66eec61bc77.
D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility: D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.CPTP sha256:201d8b8958928e322011114ae2b15914f4c31a8b8fe3112d0001b8a469cf2b43.
D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity: D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity.residual_identity sha256:503bc3b9625a01dc80e5d750b56f6c21f72fd51e069c5cd9e47a3113b48ef7d4.
D5/S3/Quantum/Recovery/KrausCompletion: D5.S3.Quantum.Recovery.KrausCompletion.completeKraus sha256:9bc1b68ac994f0016777e57b1d64c54b108e6abd905075577ce14b2a0a7b71c3; D5.S3.Quantum.Recovery.KrausCompletion.rowReset sha256:63b0c2d244c2f26eaa46ef36429ea4c9ccb72f7db37882de172d0e5045f79e31.
D5/S3/Quantum/Reduction/ProbeComponentRigidity: D5.S3.Quantum.Reduction.ProbeComponentRigidity.krausStinespring sha256:7811d010941f1b5190cefe63bcf55fd85c9a8f19b1b90465040d164ed966ec6a; D5.S3.Quantum.Reduction.ProbeComponentRigidity.kraus_inner sha256:a3b7ef371b111001ac6d2f33ac031dc327572531aeb2545bca78cae6b3923560.
D5/S3/QuantumBounds/PeritoTsirelson: D5.S3.QuantumBounds.PeritoTsirelson.maxEntangledVector sha256:0d9b796675e34d44a262b9970de30f6e14b9c29ad43fe82138028956b24f9e3f.
No module statement_id is used as a declaration identity.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25592.
The Scribe displays MatrixMap.choi_matrix by its complete coordinate expression.
The process fidelity expression is inlined literally; its existing equivalent owner
LiJiangPolarPairOptimalityRefutation.entanglementFidelity is in stratum of generality I
and cannot be imported by this G module.
The scalar and square-root bounds are for a fixed finite unit spanning family with
connected nonorthogonality graph; constants may depend on that family.
-/
import D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
import D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingCore
import D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity
import D5.S3.Quantum.Reduction.ProbeComponentRigidity
import D5.S3.Quantum.GNSMatrix
import D5.S3.QuantumBounds.PeritoTsirelson
import D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Recovery.ActualChannelAlgebra
import D5.S3.Quantum.Recovery.KrausCompletion
noncomputable section
open Matrix
open scoped BigOperators
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility (CPTP)
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
/- Source conventions from Mayer–Knill, arXiv:1805.04491v1, §II and §III.
   The source writes a pure state as |ψ⟩⟨ψ|, a channel as a CPTP linear map,
   and uses the normalized maximally entangled vector. -/
def unitInputFamily {d N : ℕ} (ψ : Fin N → Fin d → ℂ) : Prop :=
  ∀ k, star (ψ k) ⬝ᵥ ψ k = 1
def spanInputFamily {d N : ℕ} (ψ : Fin N → Fin d → ℂ) : Prop :=
  Submodule.span ℂ (Set.range ψ) = ⊤
def nonorthogonalityConnected {d N : ℕ} (ψ : Fin N → Fin d → ℂ) : Prop :=
  ∀ i j, Relation.EqvGen (fun a b => star (ψ a) ⬝ᵥ ψ b ≠ 0) i j
def survivalFidelity {d : ℕ} (Φ : MatrixMap (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) : ℝ :=
  (star ψ ⬝ᵥ (Φ (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity ψ) *ᵥ ψ)).re
def admissibleAt {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (ε : ℝ) (Φ : MatrixMap (Fin d) (Fin d) ℂ) : Prop :=
  CPTP Φ ∧ ∀ k, 1 - ε ≤ survivalFidelity Φ (ψ k)
def f {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (ε : ℝ) : ℝ :=
  1 - sInf {x : ℝ | ∃ Φ, admissibleAt ψ ε Φ ∧ x = (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ}
def obstructionSpace {d N : ℕ} (ψ : Fin N → Fin d → ℂ) : Set (Matrix (Fin d) (Fin d) ℂ) :=
  {A | ∀ k, (1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ k)) *ᵥ (A *ᵥ ψ k) = 0}
def scalarObstruction {d N : ℕ} (ψ : Fin N → Fin d → ℂ) : Prop :=
  ∀ A, A ∈ obstructionSpace ψ → ∃ z : ℂ, A = z • (1 : Matrix (Fin d) (Fin d) ℂ)
def LinearScaling {d N : ℕ} (ψ : Fin N → Fin d → ℂ) : Prop :=
  ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ → c * ε ≤ f ψ ε ∧ f ψ ε ≤ C * ε
def SqrtScaling {d N : ℕ} (ψ : Fin N → Fin d → ℂ) : Prop :=
  ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ →
      c * Real.sqrt ε ≤ f ψ ε ∧ f ψ ε ≤ C * Real.sqrt ε
def claim : Prop :=
  ∀ (d N : ℕ) (ψ : Fin N → Fin d → ℂ),
    2 ≤ d → unitInputFamily ψ → spanInputFamily ψ →
      nonorthogonalityConnected ψ →
      (scalarObstruction ψ ↔ LinearScaling ψ) ∧
      (¬ scalarObstruction ψ ↔ SqrtScaling ψ)
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
set_option maxHeartbeats 20000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
private theorem residual_iff {d : ℕ} (ψ v : Fin d → ℂ) : (1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity ψ) *ᵥ v = 0 ↔ v = (star ψ ⬝ᵥ v) • ψ := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
    Matrix.vecMulVec_mulVec]
  simp only [op_smul_eq_smul]
private theorem residual_self {d : ℕ} (ψ : Fin d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : (1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity ψ) *ᵥ ψ = 0 := by
  rw [residual_iff, hψ, one_smul]
private theorem obstruction_sub_scalar {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hψ : unitInputFamily ψ) (A : Matrix (Fin d) (Fin d) ℂ) (hA : A ∈ obstructionSpace ψ) (z : ℂ) : A - z • (1 : Matrix (Fin d) (Fin d) ℂ) ∈ obstructionSpace ψ := by
  intro k
  rw [Matrix.sub_mulVec A (z • 1) (ψ k), Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_sub, Matrix.mulVec_smul, hA k, residual_self _ (hψ k)]
  simp
private theorem traceless_obstruction {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 0 < d) (hψ : unitInputFamily ψ) (hS : ¬ scalarObstruction ψ) : ∃ A : Matrix (Fin d) (Fin d) ℂ, A ∈ obstructionSpace ψ ∧ Matrix.trace A = 0 ∧ A ≠ 0 := by
  classical
  unfold scalarObstruction at hS
  push Not at hS
  obtain ⟨B, hB, hn⟩ := hS
  let z : ℂ := Matrix.trace B / d
  refine ⟨B - z • 1, obstruction_sub_scalar ψ hψ B hB z, ?_, ?_⟩
  · rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul]
    dsimp [z]
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
    ring
  · intro h
    exact hn z (sub_eq_zero.mp h)
private theorem normalized_obstruction {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 0 < d) (hψ : unitInputFamily ψ) (hS : ¬ scalarObstruction ψ) : ∃ A : Matrix (Fin d) (Fin d) ℂ, A ∈ obstructionSpace ψ ∧ Matrix.trace A = 0 ∧ ‖A‖ = 1 := by
  obtain ⟨B, hB, ht, hn⟩ := traceless_obstruction ψ hd hψ hS
  have hn0 : ‖B‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  refine ⟨(‖B‖⁻¹ : ℂ) • B, ?_, ?_, ?_⟩
  · intro k
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, hB k, smul_zero]
  · simp [Matrix.trace_smul, ht]
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg B),
      inv_mul_cancel₀ hn0]
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
open scoped Matrix.Norms.Frobenius
private def detectionMap {d N : ℕ} (ψ : Fin N → Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ × EuclideanSpace ℂ (Fin N × Fin d) where
  toFun A := (Matrix.trace A, WithLp.toLp 2 (fun p => ((1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ p.1)) *ᵥ (A *ᵥ ψ p.1)) p.2))
  map_add' A B := by
    ext <;> simp [Matrix.trace_add, Matrix.add_mulVec, Matrix.mulVec_add]
  map_smul' c A := by
    ext <;> simp [Matrix.trace_smul, Matrix.smul_mulVec, Matrix.mulVec_smul]
private theorem scalar_detection_injective {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 0 < d) (hS : scalarObstruction ψ) : Function.Injective (detectionMap ψ) := by
  intro A B hAB
  apply sub_eq_zero.mp
  have hzero : detectionMap ψ (A - B) = 0 := by rw [map_sub, hAB, sub_self]
  have ht : Matrix.trace (A - B) = 0 := congrArg Prod.fst hzero
  have hr : A - B ∈ obstructionSpace ψ := by
    intro k
    ext i
    exact congrFun (congrArg WithLp.ofLp (congrArg Prod.snd hzero)) (k, i)
  obtain ⟨z, hz⟩ := hS (A - B) hr
  rw [hz, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at ht
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hz0 : z = 0 := (mul_eq_zero.mp ht).resolve_right hd0
  simpa [hz0] using hz
private theorem scalar_coercivity {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 0 < d) (hS : scalarObstruction ψ) : ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin d) (Fin d) ℂ, Matrix.trace A = 0 → ‖A‖ ≤ C * ‖(WithLp.toLp 2 (fun p : Fin N × Fin d => ((1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ p.1)) *ᵥ (A *ᵥ ψ p.1)) p.2) : EuclideanSpace ℂ (Fin N × Fin d))‖ := by
  obtain ⟨C, hC, hbound⟩ := (detectionMap ψ).injective_iff_antilipschitz.mp
    (scalar_detection_injective ψ hd hS)
  refine ⟨C, by exact_mod_cast hC, fun A hA => ?_⟩
  have h := ZeroHomClass.bound_of_antilipschitz (detectionMap ψ) hbound A
  simpa [detectionMap, hA, Prod.norm_def] using h
private theorem scalar_coercivity_sq {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 0 < d) (hS : scalarObstruction ψ) : ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin d) (Fin d) ℂ, Matrix.trace A = 0 → ‖A‖ ^ 2 ≤ C * ∑ k, ∑ i, ‖((1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ k)) *ᵥ (A *ᵥ ψ k)) i‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := scalar_coercivity ψ hd hS
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro A hA
  have hs := pow_le_pow_left₀ (norm_nonneg A) (hb A hA) 2
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type] using hs
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
open scoped ComplexOrder
private theorem entangled_coordinates (d : ℕ) :
    (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0) =
      D5.S3.QuantumBounds.PeritoTsirelson.maxEntangledVector (Fin d) := by
  funext ij
  simp only [D5.S3.QuantumBounds.PeritoTsirelson.maxEntangledVector, Fintype.card_fin]
private theorem process_nonneg {d : ℕ} (Φ : MatrixMap (Fin d) (Fin d) ℂ) (hΦ : CPTP Φ) : 0 ≤ (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ := by
  have hp := (MatrixMap.choi_PSD_iff_CP_map Φ).mp hΦ.1
  have hv := hp.dotProduct_mulVec_nonneg (D5.S3.QuantumBounds.PeritoTsirelson.maxEntangledVector (Fin d))
  simpa only [entangled_coordinates] using
    div_nonneg (Complex.nonneg_iff.mp hv).1 (Nat.cast_nonneg d)
private theorem fidelity_bddBelow {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (ε : ℝ) : BddBelow {x : ℝ | ∃ Φ, admissibleAt ψ ε Φ ∧ x = (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ} := by
  refine ⟨0, ?_⟩
  rintro x ⟨Φ, hΦ, rfl⟩
  exact process_nonneg Φ hΦ.1
private theorem f_lower_of_channel {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (ε : ℝ) (Φ : MatrixMap (Fin d) (Fin d) ℂ) (hΦ : admissibleAt ψ ε Φ) : 1 - (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ ≤ f ψ ε := by
  have h := csInf_le (fidelity_bddBelow ψ ε) (show (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ ∈
    {x : ℝ | ∃ Φ, admissibleAt ψ ε Φ ∧ x = (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ} from ⟨Φ, hΦ, rfl⟩)
  exact sub_le_sub_left h 1
private theorem f_upper_of_channels {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (ε B : ℝ) (hne : ∃ Φ, admissibleAt ψ ε Φ) (hB : ∀ Φ, admissibleAt ψ ε Φ → 1 - (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ ≤ B) : f ψ ε ≤ B := by
  have hset : Set.Nonempty {x : ℝ | ∃ Φ, admissibleAt ψ ε Φ ∧ x = (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ} := by
    obtain ⟨Φ, hΦ⟩ := hne
    exact ⟨(fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ, Φ, hΦ, rfl⟩
  have h := le_csInf hset (show ∀ x ∈
      {x : ℝ | ∃ Φ, admissibleAt ψ ε Φ ∧ x = (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ}, 1 - B ≤ x from by
    rintro x ⟨Φ, hΦ, rfl⟩
    linarith [hB Φ hΦ])
  unfold f
  linarith
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
private theorem scaling_exclusive {d N : ℕ} (ψ : Fin N → Fin d → ℂ) : LinearScaling ψ → ¬ SqrtScaling ψ := by
  rintro ⟨c, C, δ, hc, hC, hδ, hL⟩ ⟨b, B, η, hb, hB, hη, hS⟩
  let x := min (min δ η) (min 1 (b / (2 * C))) / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hxδ : x < δ := by
    have := min_le_left (min δ η) (min 1 (b / (2 * C)))
    have := min_le_left δ η
    dsimp [x]
    linarith
  have hxη : x < η := by
    have := min_le_left (min δ η) (min 1 (b / (2 * C)))
    have := min_le_right δ η
    dsimp [x]
    linarith
  have hx1 : x < 1 := by
    have := min_le_right (min δ η) (min 1 (b / (2 * C)))
    have := min_le_left 1 (b / (2 * C))
    dsimp [x]
    linarith
  have hxC : C * x < b := by
    have hh := min_le_right (min δ η) (min 1 (b / (2 * C)))
    have hh' := min_le_right 1 (b / (2 * C))
    have hqpos : 0 < b / (2 * C) := by positivity
    have hbound : x < b / (2 * C) := by dsimp [x]; linarith
    have := (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp hbound
    nlinarith
  have hxx : 0 < x ^ 2 := sq_pos_of_pos hx
  have hxxδ : x ^ 2 < δ := by nlinarith
  have hxxη : x ^ 2 < η := by nlinarith
  have h1 := (hL (x ^ 2) hxx hxxδ).2
  have h2 := (hS (x ^ 2) hxx hxxη).1
  rw [Real.sqrt_sq hx.le] at h2
  nlinarith
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
private theorem kraus_survival {d r : ℕ} (ψ : Fin d → ℂ) (K : Fin r → Matrix (Fin d) (Fin d) ℂ) : survivalFidelity (MatrixMap.of_kraus K K) ψ = ∑ a, ‖star ψ ⬝ᵥ (K a *ᵥ ψ)‖ ^ 2 := by
  exact D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingCore.kraus_survival ψ K
private theorem entangled_amplitude {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : star (D5.S3.QuantumBounds.PeritoTsirelson.maxEntangledVector (Fin d)) ⬝ᵥ (fun ij : Fin d × Fin d => A ij.1 ij.2) = (Real.sqrt d : ℂ)⁻¹ * Matrix.trace A := by
  classical
  simp only [D5.S3.QuantumBounds.PeritoTsirelson.maxEntangledVector, Fintype.card_fin, dotProduct, Fintype.sum_prod_type,
    Pi.star_apply, Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [Complex.star_def]
  · intro j _ hji
    simp [Ne.symm hji, Complex.star_def]
  · simp
private theorem choi_overlap {d : ℕ} {ι : Type*} [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ) (v : Fin d × Fin d → ℂ) : star v ⬝ᵥ (MatrixMap.choi_matrix (MatrixMap.of_kraus K K) *ᵥ v) = ∑ a, (Complex.normSq (star v ⬝ᵥ (fun ij => K a ij.1 ij.2)) : ℂ) := by
  rw [MatrixMap.choi_of_kraus, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun a _ => D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockSpectral.rankOneQuadratic v _
private theorem process_trace {d : ℕ} {ι : Type*} [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ) : (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) (MatrixMap.of_kraus K K) = (∑ a, Complex.normSq (Matrix.trace (K a))) / (d : ℝ) ^ 2 := by
  dsimp only
  rw [entangled_coordinates, choi_overlap]
  simp only [entangled_amplitude, Complex.re_sum, Complex.ofReal_re,
    Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal,
    Real.sq_sqrt (Nat.cast_nonneg d), Real.mul_self_sqrt (Nat.cast_nonneg d)]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, pow_two, mul_inv, mul_assoc] <;> ring
private theorem kraus_cptp {d : ℕ} {ι : Type*} [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1) : CPTP (MatrixMap.of_kraus K K) := by
  exact ⟨MatrixMap.of_kraus_isCompletelyPositive K,
    MatrixMap.IsTracePreserving.of_kraus_isTracePreserving K K hK⟩
private theorem identity_kraus {d : ℕ} : MatrixMap.of_kraus (fun _ : Fin 1 => (1 : Matrix (Fin d) (Fin d) ℂ)) (fun _ : Fin 1 => (1 : Matrix (Fin d) (Fin d) ℂ)) = LinearMap.id := by
  ext X i j
  simp [MatrixMap.of_kraus]
private theorem identity_admissible {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hψ : unitInputFamily ψ) (ε : ℝ) (hε : 0 ≤ ε) : admissibleAt ψ ε LinearMap.id := by
  constructor
  · rw [← identity_kraus]
    exact kraus_cptp _ (by simp)
  · intro k
    have hs : survivalFidelity LinearMap.id (ψ k) = 1 := by
      unfold survivalFidelity
      rw [LinearMap.id_apply,
        D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
        Matrix.vecMulVec_mulVec]
      simp [op_smul_eq_smul, hψ k]
    rw [hs]
    linarith
open scoped Matrix.Norms.Frobenius
private theorem centered_gram_trace {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) : Matrix.trace ((A - (Matrix.trace A / d) • 1)ᴴ * (A - (Matrix.trace A / d) • 1)) = Matrix.trace (Aᴴ * A) - (Complex.normSq (Matrix.trace A) : ℂ) / d := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_one, Matrix.trace_conjTranspose,
    Fintype.card_fin, smul_eq_mul, star_div₀, star_natCast]
  rw [← Complex.mul_conj (Matrix.trace A)]
  simp only [Complex.star_def]
  field_simp <;> ring
private theorem centered_frobenius_sq {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) : ‖A - (Matrix.trace A / d) • 1‖ ^ 2 = ‖A‖ ^ 2 - Complex.normSq (Matrix.trace A) / d := by
  have h := centered_gram_trace hd A
  rw [← D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace,
      ← D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace] at h
  exact_mod_cast h
private theorem kraus_process_loss {d : ℕ} {ι : Type*} [Fintype ι] (hd : 0 < d) (K : ι → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1) : 1 - (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) (MatrixMap.of_kraus K K) = (∑ a, ‖K a - (Matrix.trace (K a) / d) • 1‖ ^ 2) / d := by
  have htC : (∑ a, ((‖K a‖ ^ 2 : ℝ) : ℂ)) = (d : ℂ) := by
    simp_rw [D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace]
    rw [← Matrix.trace_sum, hK, Matrix.trace_one, Fintype.card_fin]
  have htR : ∑ a, ‖K a‖ ^ 2 = (d : ℝ) := by exact_mod_cast htC
  rw [process_trace]
  simp_rw [centered_frobenius_sq hd]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, htR]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp <;> ring
private theorem kraus_input_loss {d r : ℕ} (ψ : Fin d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1) : 1 - survivalFidelity (MatrixMap.of_kraus K K) ψ = ∑ a, ∑ i, Complex.normSq (((1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity ψ) *ᵥ (K a *ᵥ ψ)) i) := by
  have hself (v : Fin d → ℂ) : (star v ⬝ᵥ v).re = ∑ i, Complex.normSq (v i) := by
    simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hψSq : ∑ i, Complex.normSq (ψ i) = 1 := by rw [← hself, hψ]; rfl
  have htotal := D5.S3.Quantum.Reduction.ProbeComponentRigidity.kraus_inner K hK ψ ψ
  have htR : (∑ a, ∑ i, Complex.normSq ((K a *ᵥ ψ) i)) = 1 := by
    have h := congrArg Complex.re htotal
    simpa only [Complex.re_sum, hself, hψSq] using h
  have hr (a : Fin r) : (∑ i, Complex.normSq (((1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity ψ) *ᵥ (K a *ᵥ ψ)) i)) =
      (∑ i, Complex.normSq ((K a *ᵥ ψ) i)) - Complex.normSq (star ψ ⬝ᵥ (K a *ᵥ ψ)) := by
    have h := D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity.residual_identity (K a *ᵥ ψ) ψ hψSq
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
      Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct, Pi.star_apply,
      Complex.star_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  rw [kraus_survival]
  simp_rw [hr]
  rw [Finset.sum_sub_distrib, htR]
  simp only [Complex.normSq_eq_norm_sq]
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
private theorem contraction_gram_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : ‖A‖ ≤ 1) : Aᴴ * A ≤ 1 := by
  have h := CStarAlgebra.star_mul_le_algebraMap_norm_sq A
  change Aᴴ * A ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (‖A‖ ^ 2) at h
  calc
    Aᴴ * A ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (‖A‖ ^ 2) := h
    _ ≤ 1 := by
      rw [Algebra.algebraMap_eq_smul_one]
      simpa using smul_le_smul_of_nonneg_right
        (show ‖A‖ ^ 2 ≤ 1 by nlinarith [norm_nonneg A]) (show (0 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 from zero_le_one)
private theorem sqrt_completion {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : ‖A‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : (CFC.sqrt (1 - t • (Aᴴ * A)))ᴴ * CFC.sqrt (1 - t • (Aᴴ * A)) + ((Real.sqrt t : ℂ) • A)ᴴ * ((Real.sqrt t : ℂ) • A) = 1 := by
  have hAA : 0 ≤ Aᴴ * A := (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have hA1 := contraction_gram_le A hA
  have htA : t • (Aᴴ * A) ≤ (1 : Matrix (Fin d) (Fin d) ℂ) := by
    calc
      _ ≤ t • (1 : Matrix (Fin d) (Fin d) ℂ) := smul_le_smul_of_nonneg_left hA1 ht
      _ ≤ 1 := by simpa using smul_le_smul_of_nonneg_right ht1 (show (0 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 from zero_le_one)
  have hB : 0 ≤ (1 : Matrix (Fin d) (Fin d) ℂ) - t • (Aᴴ * A) := sub_nonneg.mpr htA
  have hstar : (CFC.sqrt (1 - t • (Aᴴ * A)))ᴴ = CFC.sqrt (1 - t • (Aᴴ * A)) :=
    (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq
  rw [hstar, CFC.sqrt_mul_sqrt_self _ hB]
  have hs : star (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt ht
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
  norm_cast
  module
private theorem sqrt_completion_distance {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : ‖A‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : ‖CFC.sqrt (1 - t • (Aᴴ * A)) - 1‖ ≤ t := by
  have hAA : 0 ≤ Aᴴ * A := (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have hA1 := contraction_gram_le A hA
  have htAA : 0 ≤ t • (Aᴴ * A) := smul_nonneg ht hAA
  have htA : t • (Aᴴ * A) ≤ (1 : Matrix (Fin d) (Fin d) ℂ) := by
    calc
      _ ≤ t • (1 : Matrix (Fin d) (Fin d) ℂ) := smul_le_smul_of_nonneg_left hA1 ht
      _ ≤ 1 := by simpa using smul_le_smul_of_nonneg_right ht1 (show (0 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 from zero_le_one)
  let B := (1 : Matrix (Fin d) (Fin d) ℂ) - t • (Aᴴ * A)
  have hB : 0 ≤ B := sub_nonneg.mpr htA
  have hB1 : B ≤ 1 := sub_le_self 1 htAA
  have hroot1 : CFC.sqrt B ≤ (1 : Matrix (Fin d) (Fin d) ℂ) := by
    simpa using CFC.monotone_sqrt hB1
  have hBnorm : ‖B‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg B hB).mpr hB1
  have hBroot : B ≤ CFC.sqrt B := CStarAlgebra.self_le_sqrt_of_nonneg_of_norm_le_one hB hBnorm
  rw [norm_sub_rev]
  apply (CStarAlgebra.norm_le_iff_le_algebraMap (1 - CFC.sqrt B) ht (sub_nonneg.mpr hroot1)).mpr
  rw [Algebra.algebraMap_eq_smul_one]
  calc
    1 - CFC.sqrt B ≤ 1 - B := sub_le_sub_left hBroot 1
    _ = t • (Aᴴ * A) := by dsimp [B]; abel
    _ ≤ t • (1 : Matrix (Fin d) (Fin d) ℂ) := smul_le_smul_of_nonneg_left hA1 ht
private theorem residual_contraction {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (hP : IsStarProjection P) (v : Fin d → ℂ) : ‖(WithLp.toLp 2 ((1 - P) *ᵥ v) : EuclideanSpace ℂ (Fin d))‖ ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d))‖ := by
  calc
    _ ≤ ‖(1 : Matrix (Fin d) (Fin d) ℂ) - P‖ *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d))‖ := by
      simpa using Matrix.l2_opNorm_mulVec (1 - P) (WithLp.toLp 2 v)
    _ ≤ 1 * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d))‖ :=
      mul_le_mul_of_nonneg_right (IsStarProjection.norm_le _ hP.one_sub) (norm_nonneg _)
    _ = _ := one_mul _
private theorem completion_tested_residual {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : ‖A‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (P : Matrix (Fin d) (Fin d) ℂ) (hP : IsStarProjection P) (v : Fin d → ℂ) (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d))‖ ≤ 1) (hv0 : (1 - P) *ᵥ v = 0) : ‖(WithLp.toLp 2 ((1 - P) *ᵥ (CFC.sqrt (1 - t • (Aᴴ * A)) *ᵥ v)) : EuclideanSpace ℂ (Fin d))‖ ≤ t := by
  have he : (1 - P) *ᵥ (CFC.sqrt (1 - t • (Aᴴ * A)) *ᵥ v) =
      (1 - P) *ᵥ ((CFC.sqrt (1 - t • (Aᴴ * A)) - 1) *ᵥ v) := by
    rw [Matrix.sub_mulVec (CFC.sqrt (1 - t • (Aᴴ * A))) (1 : Matrix (Fin d) (Fin d) ℂ) v,
      Matrix.one_mulVec, Matrix.mulVec_sub, hv0, sub_zero]
  rw [he]
  calc
    _ ≤ ‖(WithLp.toLp 2 ((CFC.sqrt (1 - t • (Aᴴ * A)) - 1) *ᵥ v) :
        EuclideanSpace ℂ (Fin d))‖ := residual_contraction P hP _
    _ ≤ ‖CFC.sqrt (1 - t • (Aᴴ * A)) - 1‖ *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d))‖ := by
      simpa using Matrix.l2_opNorm_mulVec (CFC.sqrt (1 - t • (Aᴴ * A)) - 1)
        (WithLp.toLp 2 v)
    _ ≤ t * 1 := mul_le_mul (sqrt_completion_distance A hA t ht ht1) hv (norm_nonneg _) ht
    _ = t := mul_one t
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
private theorem pair_distance_of_gram_defect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ^ 2 ≤ 2 * ‖1 - inner ℂ x y‖ := by
  have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hy2 : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
  have hr := Complex.re_le_norm (1 - inner ℂ x y)
  simp only [Complex.sub_re, Complex.one_re] at hr
  rw [norm_sub_sq (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex]
  nlinarith
private theorem overlap_distance_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (g : ℂ) (hg : g ≠ 0) (D : ℝ) (hD : ‖g * (1 - inner ℂ x y)‖ ≤ D) : ‖x - y‖ ^ 2 ≤ 2 * D / ‖g‖ := by
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have h := pair_distance_of_gram_defect x y hx hy
  rw [norm_mul] at hD
  apply (le_div_iff₀ hgpos).mpr
  nlinarith
private theorem gram_defect_from_residuals {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (a b : E) (u v ri rj : F) (g : ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hri : ‖ri‖ ^ 2 ≤ ε) (hrj : ‖rj‖ ^ 2 ≤ ε) (he : g * (1 - inner ℂ a b) = inner ℂ u rj + inner ℂ ri v + inner ℂ ri rj) : ‖g * (1 - inner ℂ a b)‖ ≤ 2 * Real.sqrt ε + ε := by
  have hri' : ‖ri‖ ≤ Real.sqrt ε := Real.le_sqrt_of_sq_le hri
  have hrj' : ‖rj‖ ≤ Real.sqrt ε := Real.le_sqrt_of_sq_le hrj
  have hb1 : ‖inner ℂ u rj‖ ≤ Real.sqrt ε := by
    exact (norm_inner_le_norm u rj).trans (by
      simpa using mul_le_mul hu hrj' (norm_nonneg rj) (show (0 : ℝ) ≤ 1 by norm_num))
  have hb2 : ‖inner ℂ ri v‖ ≤ Real.sqrt ε := by
    exact (norm_inner_le_norm ri v).trans (by
      simpa using mul_le_mul hri' hv (norm_nonneg v) (Real.sqrt_nonneg ε))
  have hb3 : ‖inner ℂ ri rj‖ ≤ ε := by
    apply (norm_inner_le_norm ri rj).trans
    have hm := mul_le_mul hri' hrj' (norm_nonneg rj) (Real.sqrt_nonneg ε)
    simpa only [Real.mul_self_sqrt hε] using hm
  rw [he]
  have ht1 := norm_add_le (inner ℂ u rj + inner ℂ ri v) (inner ℂ ri rj)
  have ht2 := norm_add_le (inner ℂ u rj) (inner ℂ ri v)
  linarith

end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
open Matrix
open scoped Matrix.Norms.Frobenius
private def evaluationMap {d N : ℕ} (ψ : Fin N → Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin N × Fin d) where
  toFun A := WithLp.toLp 2 (fun p => (A *ᵥ ψ p.1) p.2)
  map_add' A B := by
    apply WithLp.ofLp_injective
    ext p
    simp [Matrix.add_mulVec]
  map_smul' c A := by
    apply WithLp.ofLp_injective
    ext p
    simp [Matrix.smul_mulVec]
private theorem evaluation_injective {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hspan : Submodule.span ℂ (Set.range ψ) = ⊤) : Function.Injective (evaluationMap ψ) := by
  intro A B hAB
  have heq : A.mulVecLin = B.mulVecLin := by
    apply LinearMap.ext_on_range hspan
    intro k
    ext i
    exact congrFun (congrArg WithLp.ofLp hAB) (k, i)
  exact Matrix.ext_iff_mulVec.mpr (fun v => LinearMap.congr_fun heq v)
private theorem spanning_evaluation_coercivity {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hspan : Submodule.span ℂ (Set.range ψ) = ⊤) : ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin d) (Fin d) ℂ, ‖A‖ ≤ C * ‖evaluationMap ψ A‖ := by
  obtain ⟨C, hC, hb⟩ := (evaluationMap ψ).injective_iff_antilipschitz.mp
    (evaluation_injective ψ hspan)
  refine ⟨C, by exact_mod_cast hC, ?_⟩
  intro A
  exact ZeroHomClass.bound_of_antilipschitz (evaluationMap ψ) hb A
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
private theorem completed_obstruction {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 0 < d) (hψ : unitInputFamily ψ) (hS : ¬ scalarObstruction ψ) : ∃ A : Matrix (Fin d) (Fin d) ℂ, A ∈ obstructionSpace ψ ∧ Matrix.trace A = 0 ∧ ‖A‖ = 1 ∧ A ≠ 0 ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (CFC.sqrt (1 - t • (Aᴴ * A)))ᴴ * CFC.sqrt (1 - t • (Aᴴ * A)) + ((Real.sqrt t : ℂ) • A)ᴴ * ((Real.sqrt t : ℂ) • A) = 1 ∧ ‖CFC.sqrt (1 - t • (Aᴴ * A)) - 1‖ ≤ t ∧ ∀ k, (1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ k)) *ᵥ (((Real.sqrt t : ℂ) • A) *ᵥ ψ k) = 0 ∧ ‖(WithLp.toLp 2 ((1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ k)) *ᵥ (CFC.sqrt (1 - t • (Aᴴ * A)) *ᵥ ψ k)) : EuclideanSpace ℂ (Fin d))‖ ≤ t := by
  obtain ⟨A, hA, htr, hn⟩ := normalized_obstruction ψ hd hψ hS
  have hA0 : A ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
  refine ⟨A, hA, htr, hn, hA0, ?_⟩
  intro t ht ht1
  refine ⟨sqrt_completion A hn.le t ht ht1,
    sqrt_completion_distance A hn.le t ht ht1, ?_⟩
  intro k
  constructor
  · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, hA k, smul_zero]
  · have hP : IsStarProjection (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ k)) := by
      refine ⟨(D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake
        (ψ k) (hψ k) 1).1, ?_⟩
      exact (Matrix.posSemidef_vecMulVec_self_star (ψ k)).isHermitian
    have hinner : inner ℂ (WithLp.toLp 2 (ψ k) : EuclideanSpace ℂ (Fin d))
        (WithLp.toLp 2 (ψ k)) = 1 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      exact hψ k
    rw [inner_self_eq_norm_sq_to_K] at hinner
    have hsq : ‖(WithLp.toLp 2 (ψ k) : EuclideanSpace ℂ (Fin d))‖ ^ 2 = 1 := by
      have h := congrArg Complex.re hinner
      simpa only [RCLike.ofReal_eq_complex_ofReal, pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, Complex.one_re] using h
    have hnorm : ‖(WithLp.toLp 2 (ψ k) : EuclideanSpace ℂ (Fin d))‖ ≤ 1 := by
      nlinarith [norm_nonneg (WithLp.toLp 2 (ψ k) : EuclideanSpace ℂ (Fin d))]
    exact completion_tested_residual A hn.le t ht ht1 _ hP _ hnorm
      (residual_self _ (hψ k))
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
open scoped ComplexOrder MatrixOrder
private theorem sqrt_smul_gram {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (p : ℝ) (hp : 0 ≤ p) : ((Real.sqrt p : ℂ) • B)ᴴ * ((Real.sqrt p : ℂ) • B) = (p : ℂ) • (Bᴴ * B) := by
  have hs : star (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt hp
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
set_option maxHeartbeats 800000 in
private theorem reset_complete {d : ℕ} (v : Fin d) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : (∑ a, ((fun i : Fin (d + 1) => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus (fun _ : Fin 1 => (Real.sqrt (1-p) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i)) a)ᴴ * (fun i : Fin (d + 1) => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus (fun _ : Fin 1 => (Real.sqrt (1-p) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i)) a) = 1 := by
  have ht : D5.S3.Quantum.Recovery.KrausCompletion.rowReset v
      ((Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) =
      (fun j => (Real.sqrt p : ℂ) • Matrix.single v j 1) := by
    funext j
    simp [D5.S3.Quantum.Recovery.KrausCompletion.rowReset]
  have hPcomp :
      1 - (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) =
        (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    module
  simp only [D5.S3.Quantum.Recovery.KrausCompletion.completeKraus, hPcomp, ht,
    Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, Sum.elim_inl, Sum.elim_inr]
  rw [sqrt_smul_gram _ _ (sub_nonneg.mpr hp1)]
  simp_rw [sqrt_smul_gram _ _ hp]
  simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.conjTranspose_single,
    star_one, Matrix.single_mul_single_same, mul_one]
  rw [← Finset.smul_sum, Matrix.sum_single_one]
  push_cast
  module
set_option maxHeartbeats 800000 in
private theorem reset_admissible {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hψ : unitInputFamily ψ) (v : Fin d) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : admissibleAt ψ p (MatrixMap.of_kraus ((fun i : Fin (d + 1) => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus (fun _ : Fin 1 => (Real.sqrt (1-p) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i))) ((fun i : Fin (d + 1) => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus (fun _ : Fin 1 => (Real.sqrt (1-p) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i)))) := by
  refine ⟨kraus_cptp _ (reset_complete v p hp hp1), ?_⟩
  intro k
  have hs : ‖star (ψ k) ⬝ᵥ ((fun i : Fin (d + 1) => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus (fun _ : Fin 1 => (Real.sqrt (1-p) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i)) 0 *ᵥ ψ k)‖ ^ 2 = 1 - p := by
    simp [D5.S3.Quantum.Recovery.KrausCompletion.completeKraus, D5.S3.Quantum.Recovery.KrausCompletion.rowReset, sub_sub_cancel, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul, hψ k, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (sub_nonneg.mpr hp1)]
  rw [kraus_survival, Fin.sum_univ_succ, hs]
  have hn : 0 ≤ ∑ a : Fin d,
      ‖star (ψ k) ⬝ᵥ ((fun i : Fin (d + 1) => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus (fun _ : Fin 1 => (Real.sqrt (1-p) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i)) a.succ *ᵥ ψ k)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith
set_option maxHeartbeats 800000 in
private theorem reset_process {d : ℕ} (hd : 0 < d) (v : Fin d) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) (MatrixMap.of_kraus ((fun i : Fin (d + 1) => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus (fun _ : Fin 1 => (Real.sqrt (1-p) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i))) ((fun i : Fin (d + 1) => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus (fun _ : Fin 1 => (Real.sqrt (1-p) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i)))) = 1 - p + p / (d : ℝ) ^ 2 := by
  have h0 : Complex.normSq (Matrix.trace ((fun i : Fin (d + 1) => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus (fun _ : Fin 1 => (Real.sqrt (1-p) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i)) 0)) =
      (1 - p) * (d : ℝ) ^ 2 := by
    simp [D5.S3.Quantum.Recovery.KrausCompletion.completeKraus, D5.S3.Quantum.Recovery.KrausCompletion.rowReset, sub_sub_cancel, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, Real.mul_self_sqrt (sub_nonneg.mpr hp1),
      Complex.normSq_natCast, pow_two]
  have h1 (j : Fin d) : Complex.normSq (Matrix.trace ((fun i : Fin (d + 1) => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus (fun _ : Fin 1 => (Real.sqrt (1-p) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - (Real.sqrt p : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i)) j.succ)) =
      if j = v then p else 0 := by
    by_cases h : j = v
    · subst j
      simp [D5.S3.Quantum.Recovery.KrausCompletion.completeKraus, D5.S3.Quantum.Recovery.KrausCompletion.rowReset, sub_sub_cancel, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Matrix.trace_single_eq_same,
        Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hp]
    · simp [D5.S3.Quantum.Recovery.KrausCompletion.completeKraus, D5.S3.Quantum.Recovery.KrausCompletion.rowReset, sub_sub_cancel, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul,
        Matrix.trace_single_eq_of_ne v j (Real.sqrt p : ℂ) (Ne.symm h), h]
  rw [process_trace, Fin.sum_univ_succ, h0]
  simp_rw [h1]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp <;> ring
set_option maxHeartbeats 800000 in
private theorem universal_linear_lower {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 2 ≤ d) (hψ : unitInputFamily ψ) : ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → c * ε ≤ f ψ ε := by
  have hdpos : 0 < d := Nat.zero_lt_of_lt hd
  have hdR : (2 : ℝ) ≤ d := Nat.ofNat_le_cast.mpr hd
  have hsq : 1 < (d : ℝ) ^ 2 := by nlinarith
  have hc : 0 < 1 - 1 / (d : ℝ) ^ 2 := by
    have : 1 / (d : ℝ) ^ 2 < 1 := (div_lt_one (by positivity)).mpr hsq
    linarith
  refine ⟨1 - 1 / (d : ℝ) ^ 2, 1, hc, by norm_num, ?_⟩
  intro ε hε hε1
  let v : Fin d := ⟨0, hdpos⟩
  let K : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ :=
    fun i => D5.S3.Quantum.Recovery.KrausCompletion.completeKraus
      (fun _ : Fin 1 => (Real.sqrt (1 - ε) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))
      (1 - (Real.sqrt ε : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) v
      (Fin.cases (Sum.inl (0 : Fin 1)) (fun j => Sum.inr j) i)
  have h := f_lower_of_channel ψ ε
    (MatrixMap.of_kraus K K) (by
      simpa only [K] using reset_admissible ψ hψ v ε hε.le hε1.le)
  have hproc :
      (fun Φ : MatrixMap (Fin d) (Fin d) ℂ =>
        ((star ((fun ij : Fin d × Fin d =>
          if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ
          (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d =>
            if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d)
        (MatrixMap.of_kraus K K) = 1 - ε + ε / (d : ℝ) ^ 2 := by
    simpa only [K] using reset_process hdpos v ε hε.le hε1.le
  rw [hproc] at h
  convert h using 1 <;> ring
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
open scoped Matrix.Norms.Frobenius
private theorem finite_kraus_of_cptp {d : ℕ} (Φ : MatrixMap (Fin d) (Fin d) ℂ) (hΦ : CPTP Φ) : ∃ K : Fin (Fintype.card (Fin d × Fin d)) → Matrix (Fin d) (Fin d) ℂ, MatrixMap.of_kraus K K = Φ ∧ (∑ a, (K a)ᴴ * K a) = 1 := by
  classical
  obtain ⟨B, hB⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Φ hΦ.1
  let e := Fintype.equivFin (Fin d × Fin d)
  let K := B ∘ e.symm
  have heq : MatrixMap.of_kraus K K = Φ := by
    rw [hB]
    ext X i j
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.sum_apply]
    simpa only [K, Function.comp_apply] using
      e.symm.sum_comp (fun a => (B a * X * (B a)ᴴ) i j)
  refine ⟨K, heq, ?_⟩
  apply Original8340Global.kraus_normalization_from_actual_trace
  intro X
  have htrace := hΦ.2 X
  rw [← heq] at htrace
  simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk] using htrace
private theorem scalar_channel_upper {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 0 < d) (hψ : unitInputFamily ψ) (hS : scalarObstruction ψ) : ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ Φ : MatrixMap (Fin d) (Fin d) ℂ, admissibleAt ψ ε Φ → 1 - (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ ≤ C * ε := by
  obtain ⟨C, hC, hb⟩ := scalar_coercivity_sq ψ hd hS
  have hdR : (0 : ℝ) < d := Nat.cast_pos'.mpr hd
  have hdC : (d : ℂ) ≠ 0 := Complex.ne_zero_of_re_pos hdR
  refine ⟨C * (N + 1) / d, by positivity, ?_⟩
  intro ε hε Φ hAdm
  let r := Fintype.card (Fin d × Fin d)
  obtain ⟨K, hΦ, hK⟩ := finite_kraus_of_cptp Φ hAdm.1
  have htr (a : Fin r) : Matrix.trace (K a - (Matrix.trace (K a) / d) • 1) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul]
    field_simp
    ring
  have hres (a : Fin r) (k : Fin N) :
      (1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ k)) *ᵥ ((K a - (Matrix.trace (K a) / d) • 1) *ᵥ ψ k) =
        (1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ k)) *ᵥ (K a *ᵥ ψ k) := by
    rw [Matrix.sub_mulVec (K a) ((Matrix.trace (K a) / d) • 1) (ψ k),
      Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
      residual_self _ (hψ k), smul_zero, sub_zero]
  have hsum : (∑ a, ‖K a - (Matrix.trace (K a) / d) • 1‖ ^ 2) ≤
      C * ∑ k, (1 - survivalFidelity Φ (ψ k)) := by
    calc
      _ ≤ ∑ a, C * ∑ k, ∑ i,
          ‖((1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ k)) *ᵥ (K a *ᵥ ψ k)) i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [hres] using hb (K a - (Matrix.trace (K a) / d) • 1) (htr a)
      _ = C * ∑ k, (1 - survivalFidelity Φ (ψ k)) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [← hΦ, kraus_input_loss (ψ k) (hψ k) K hK]
        simp only [Complex.normSq_eq_norm_sq]
  have hinputs : (∑ k, (1 - survivalFidelity Φ (ψ k))) ≤ (N : ℝ) * ε := by
    calc
      _ ≤ ∑ k : Fin N, ε := Finset.sum_le_sum fun k _ => by linarith [hAdm.2 k]
      _ = (N : ℝ) * ε := by simp
  calc
    1 - (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ = (∑ a, ‖K a - (Matrix.trace (K a) / d) • 1‖ ^ 2) / d := by
      rw [← hΦ, kraus_process_loss hd K hK]
    _ ≤ (C * (N + 1) * ε) / d := by
      apply (div_le_div_iff_of_pos_right hdR).mpr
      have hh := hsum.trans (mul_le_mul_of_nonneg_left hinputs hC.le)
      nlinarith [mul_nonneg hC.le hε]
    _ = (C * (N + 1) / d) * ε := by ring
private theorem scalar_implies_linear {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 2 ≤ d) (hψ : unitInputFamily ψ) (hS : scalarObstruction ψ) : LinearScaling ψ := by
  have hdpos : 0 < d := Nat.zero_lt_of_lt hd
  obtain ⟨c, δ, hc, hδ, hl⟩ := universal_linear_lower ψ hd hψ
  obtain ⟨C, hC, hu⟩ := scalar_channel_upper ψ hdpos hψ hS
  refine ⟨c, C, δ, hc, hC, hδ, ?_⟩
  intro ε hε hεδ
  refine ⟨hl ε hε hεδ, ?_⟩
  apply f_upper_of_channels ψ ε (C * ε)
  · exact ⟨LinearMap.id, identity_admissible ψ hψ ε hε.le⟩
  · exact hu ε hε.le
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
open scoped Matrix.Norms.Frobenius
private theorem nonscalar_sqrt_lower {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 0 < d) (hψ : unitInputFamily ψ) (hS : ¬ scalarObstruction ψ) : ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → c * Real.sqrt ε ≤ f ψ ε := by
  obtain ⟨A, hA, htr, hn, hA0, hw⟩ := completed_obstruction ψ hd hψ hS
  have hAF : 0 < ‖A‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hA0)
  have hdR : (0 : ℝ) < d := Nat.cast_pos'.mpr hd
  refine ⟨‖A‖ ^ 2 / d, 1, div_pos hAF hdR, by norm_num, ?_⟩
  intro ε hε hε1
  let t := Real.sqrt ε
  have ht : 0 ≤ t := Real.sqrt_nonneg ε
  have ht1 : t ≤ 1 := by
    dsimp [t]
    nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
  have ht2 : t ^ 2 = ε := Real.sq_sqrt hε.le
  let K : Fin 2 → Matrix (Fin d) (Fin d) ℂ :=
    ![CFC.sqrt (1 - t • (Aᴴ * A)), (Real.sqrt t : ℂ) • A]
  have hwt := hw t ht ht1
  have hK : (∑ a, (K a)ᴴ * K a) = 1 := by
    simpa only [Fin.sum_univ_two, K, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using hwt.1
  have hAdm : admissibleAt ψ ε (MatrixMap.of_kraus K K) := by
    refine ⟨kraus_cptp K hK, ?_⟩
    intro k
    have hr0 := (hwt.2.2 k).2
    have hr1 := (hwt.2.2 k).1
    have hs := pow_le_pow_left₀
      (norm_nonneg (WithLp.toLp 2 ((1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (ψ k)) *ᵥ
        (CFC.sqrt (1 - t • (Aᴴ * A)) *ᵥ ψ k)) : EuclideanSpace ℂ (Fin d))) hr0 2
    rw [EuclideanSpace.norm_sq_eq, ht2] at hs
    have hLoss : 1 - survivalFidelity (MatrixMap.of_kraus K K) (ψ k) ≤ ε := by
      rw [kraus_input_loss (ψ k) (hψ k) K hK]
      simpa only [Fin.sum_univ_two, K, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, hr1, Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero,
        add_zero, Complex.normSq_eq_norm_sq, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hs
    linarith
  have httrace : Matrix.trace (K 1) = 0 := by
    simp [K, Matrix.trace_smul, htr]
  have htNorm : ‖K 1‖ ^ 2 = t * ‖A‖ ^ 2 := by
    simp only [K, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, norm_smul, mul_pow,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ht]
  have hLoss : t * ‖A‖ ^ 2 / d ≤ 1 - (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) (MatrixMap.of_kraus K K) := by
    rw [kraus_process_loss hd K hK, Fin.sum_univ_two, httrace, zero_div, zero_smul,
      sub_zero, htNorm]
    apply (div_le_div_iff_of_pos_right hdR).mpr
    nlinarith [sq_nonneg ‖K 0 - (Matrix.trace (K 0) / d) • 1‖]
  calc
    (‖A‖ ^ 2 / d) * Real.sqrt ε = t * ‖A‖ ^ 2 / d := by dsimp [t]; ring
    _ ≤ 1 - (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) (MatrixMap.of_kraus K K) := hLoss
    _ ≤ f ψ ε := f_lower_of_channel ψ ε _ hAdm
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
open scoped Matrix.Norms.Frobenius
private def envVector {r d : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) : EuclideanSpace ℂ (Fin r) :=
  WithLp.toLp 2 (fun a => star x ⬝ᵥ (K a *ᵥ x))
private def residualVector {r d : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) : EuclideanSpace ℂ (Fin r × Fin d) :=
  WithLp.toLp 2 (fun p => ((1 - D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity x) *ᵥ (K p.1 *ᵥ x)) p.2)
private theorem envTensor_inner {r d : ℕ} (a b : EuclideanSpace ℂ (Fin r)) (x y : Fin d → ℂ) : inner ℂ ((WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp a) x)))) ((WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp b) y)))) = (inner ℂ a b) * (star x ⬝ᵥ y) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Function.uncurry, Matrix.vecMulVec_apply, dotProduct,
    Pi.star_apply, WithLp.ofLp_toLp, Fintype.sum_prod_type, star_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
private theorem envTensor_norm_sq {r d : ℕ} (a : EuclideanSpace ℂ (Fin r)) (x : Fin d → ℂ) (hx : star x ⬝ᵥ x = 1) : ‖(WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp a) x)))‖ ^ 2 = ‖a‖ ^ 2 := by
  have h := envTensor_inner a a x x
  rw [hx, mul_one, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  simpa only [RCLike.ofReal_eq_complex_ofReal, pow_two, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using congrArg Complex.re h
private theorem stinespring_decomposition {r d : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1) (x : Fin d → ℂ) : D5.S3.Quantum.Reduction.ProbeComponentRigidity.krausStinespring K hK (WithLp.toLp 2 x) = (WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp (envVector K x)) x))) + residualVector K x := by
  apply WithLp.ofLp_injective
  ext p
  change (K p.1 *ᵥ x) p.2 = _
  simp only [Function.uncurry, Matrix.vecMulVec_apply, envVector, residualVector, WithLp.ofLp_add, WithLp.ofLp_toLp,
    Pi.add_apply, Matrix.sub_mulVec, Matrix.one_mulVec, D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring
private theorem envVector_norm_sq {r d : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) : ‖envVector K x‖ ^ 2 = survivalFidelity (MatrixMap.of_kraus K K) x := by
  rw [kraus_survival, EuclideanSpace.norm_sq_eq]
  rfl
private theorem residualVector_norm_sq {r d : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1) (x : Fin d → ℂ) (hx : star x ⬝ᵥ x = 1) : ‖residualVector K x‖ ^ 2 = 1 - survivalFidelity (MatrixMap.of_kraus K K) x := by
  rw [kraus_input_loss x hx K hK, EuclideanSpace.norm_sq_eq]
  simp only [residualVector, Fintype.sum_prod_type, Complex.normSq_eq_norm_sq]
private theorem channel_gram_defect {r d N : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ : Fin N → Fin d → ℂ) (hψ : unitInputFamily ψ) (ε : ℝ) (hε : 0 ≤ ε) (htest : ∀ k, 1 - ε ≤ survivalFidelity (MatrixMap.of_kraus K K) (ψ k)) : (∀ k, ‖envVector K (ψ k)‖ ≤ 1) ∧ ∀ i j, ‖(star (ψ i) ⬝ᵥ ψ j) * (1 - inner ℂ (envVector K (ψ i)) (envVector K (ψ j)))‖ ≤ 2 * Real.sqrt ε + ε := by
  have hr (k) : ‖residualVector K (ψ k)‖ ^ 2 ≤ ε := by
    rw [residualVector_norm_sq K hK _ (hψ k)]
    linarith [htest k]
  have ha (k) : ‖envVector K (ψ k)‖ ≤ 1 := by
    have hh := sq_nonneg ‖residualVector K (ψ k)‖
    rw [residualVector_norm_sq K hK _ (hψ k)] at hh
    rw [← envVector_norm_sq] at hh
    nlinarith [norm_nonneg (envVector K (ψ k))]
  refine ⟨ha, ?_⟩
  intro i j
  have hu (k) : ‖(WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp (envVector K (ψ k))) (ψ k))))‖ ≤ 1 := by
    have hh := envTensor_norm_sq (envVector K (ψ k)) (ψ k) (hψ k)
    nlinarith [ha k, norm_nonneg (envVector K (ψ k)),
      norm_nonneg ((WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp (envVector K (ψ k))) (ψ k)))))]
  apply gram_defect_from_residuals _ _
    ((WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp (envVector K (ψ i))) (ψ i)))))
    ((WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp (envVector K (ψ j))) (ψ j)))))
    (residualVector K (ψ i)) (residualVector K (ψ j)) _ ε hε
    (hu i) (hu j) (hr i) (hr j)
  have he := (D5.S3.Quantum.Reduction.ProbeComponentRigidity.krausStinespring K hK).inner_map_map
    (WithLp.toLp 2 (ψ i)) (WithLp.toLp 2 (ψ j))
  rw [stinespring_decomposition, stinespring_decomposition,
    inner_add_left, inner_add_right, inner_add_right, envTensor_inner] at he
  have hsrc : inner ℂ (WithLp.toLp 2 (ψ i) : EuclideanSpace ℂ (Fin d))
      (WithLp.toLp 2 (ψ j)) = star (ψ i) ⬝ᵥ ψ j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hsrc] at he
  linear_combination -he
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
open scoped Matrix.Norms.Frobenius
private theorem centered_minimum {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) (z : ℂ) : ‖A - (Matrix.trace A / d) • 1‖ ^ 2 ≤ ‖A - z • 1‖ ^ 2 := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos'.mpr hd
  have hdC : (d : ℂ) ≠ 0 := Complex.ne_zero_of_re_pos hdR
  have he : (A - z • (1 : Matrix (Fin d) (Fin d) ℂ)) -
      (Matrix.trace (A - z • (1 : Matrix (Fin d) (Fin d) ℂ)) / (d : ℂ)) •
        (1 : Matrix (Fin d) (Fin d) ℂ) =
      A - (Matrix.trace A / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul, sub_div, mul_div_cancel_right₀ z hdC, sub_smul]
    module
  have h := centered_frobenius_sq hd (A - z • 1)
  rw [he] at h
  have hh : 0 ≤ Complex.normSq (Matrix.trace (A - z • 1)) / d :=
    div_nonneg (Complex.normSq_nonneg _) hdR.le
  linarith
set_option maxHeartbeats 800000 in
private theorem general_channel_upper {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 2 ≤ d) (hψ : unitInputFamily ψ) (hspan : spanInputFamily ψ) (hconn : nonorthogonalityConnected ψ) : ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ Φ : MatrixMap (Fin d) (Fin d) ℂ, admissibleAt ψ ε Φ → 1 - (fun Φ : MatrixMap (Fin d) (Fin d) ℂ => ((star ((fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))) ⬝ᵥ       (MatrixMap.choi_matrix Φ *ᵥ (fun ij : Fin d × Fin d => if ij.1 = ij.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0))).re / d) Φ ≤ C * Real.sqrt ε := by
  classical
  letI : NeZero d := ⟨by omega⟩
  have hdpos : 0 < d := Nat.zero_lt_of_lt hd
  have hdR : (0 : ℝ) < d := Nat.cast_pos'.mpr hdpos
  have hN : 0 < N := by
    by_contra hn
    have hn0 : N = 0 := Nat.eq_zero_of_not_pos hn
    subst N
    have hrange : Set.range ψ = ∅ := range_empty ψ
    have hb : (⊥ : Submodule ℂ (Fin d → ℂ)) = ⊤ := by
      simpa only [spanInputFamily, hrange, Submodule.span_empty] using hspan
    exact bot_ne_top hb
  let k₀ : Fin N := ⟨0, hN⟩
  let r := Fintype.card (Fin d × Fin d)
  obtain ⟨G, hG, hg⟩ := MayerKnillInfidelityScalingCore.finite_graph_squared_distance_bound
    (E := EuclideanSpace ℂ (Fin r)) (fun i j => star (ψ i) ⬝ᵥ ψ j ≠ 0) hconn
  obtain ⟨B, hB, hb⟩ := spanning_evaluation_coercivity ψ hspan
  let M : ℝ := 1 + ∑ i, ∑ j, ‖star (ψ i) ⬝ᵥ ψ j‖⁻¹
  have hM : 0 < M := by
    dsimp [M]
    positivity
  let L := G * (2 * M)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨B ^ 2 * (N + 1) * (2 + 6 * L) / d, by positivity, ?_⟩
  intro ε hε hε1 Φ hAdm
  obtain ⟨K, hΦ, hK⟩ := finite_kraus_of_cptp Φ hAdm.1
  have htests : ∀ k, 1 - ε ≤ survivalFidelity (MatrixMap.of_kraus K K) (ψ k) := by
    simpa only [hΦ] using hAdm.2
  obtain ⟨ha, hgram⟩ := channel_gram_defect K hK ψ hψ ε hε.le htests
  let D := 2 * Real.sqrt ε + ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hedge : ∀ i j, star (ψ i) ⬝ᵥ ψ j ≠ 0 →
      ‖envVector K (ψ i) - envVector K (ψ j)‖ ^ 2 ≤ (2 * M) * D := by
    intro i j hij
    have hh := overlap_distance_bound _ _ (ha i) (ha j) _ hij D (hgram i j)
    have h1 : ‖star (ψ i) ⬝ᵥ ψ j‖⁻¹ ≤ ∑ b, ‖star (ψ i) ⬝ᵥ ψ b‖⁻¹ :=
      Finset.single_le_sum (fun b _ => inv_nonneg.mpr (norm_nonneg (star (ψ i) ⬝ᵥ ψ b))) (Finset.mem_univ j)
    have h2 : (∑ b, ‖star (ψ i) ⬝ᵥ ψ b‖⁻¹) ≤
        ∑ a, ∑ b, ‖star (ψ a) ⬝ᵥ ψ b‖⁻¹ :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => inv_nonneg.mpr (norm_nonneg (star (ψ a) ⬝ᵥ ψ b)))
        (Finset.mem_univ i)
    have hiM : ‖star (ψ i) ⬝ᵥ ψ j‖⁻¹ ≤ M := by dsimp [M]; linarith
    exact hh.trans (by rw [div_eq_mul_inv]; nlinarith)
  have hdist (i j : Fin N) : ‖envVector K (ψ i) - envVector K (ψ j)‖ ^ 2 ≤ L * D := by
    simpa only [L, mul_assoc] using hg (fun k => envVector K (ψ k)) ((2 * M) * D)
      (mul_nonneg (by positivity) hD) hedge i j
  let W (k : Fin N) := (WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp (envVector K (ψ k) - envVector K (ψ k₀))) (ψ k)))) +
    residualVector K (ψ k)
  have hW (k : Fin N) : ‖W k‖ ^ 2 ≤ 2 * ε + 2 * L * D := by
    have ht := norm_add_le ((WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp (envVector K (ψ k) - envVector K (ψ k₀))) (ψ k)))))
      (residualVector K (ψ k))
    have hs := pow_le_pow_left₀ (norm_nonneg (W k)) ht 2
    have hten := envTensor_norm_sq (envVector K (ψ k) - envVector K (ψ k₀)) (ψ k) (hψ k)
    have hr : ‖residualVector K (ψ k)‖ ^ 2 ≤ ε := by
      rw [residualVector_norm_sq K hK _ (hψ k)]
      linarith [htests k]
    nlinarith [hdist k k₀, sq_nonneg
      (‖(WithLp.toLp 2 (Function.uncurry (Matrix.vecMulVec (WithLp.ofLp (envVector K (ψ k) - envVector K (ψ k₀))) (ψ k))))‖ - ‖residualVector K (ψ k)‖)]
  have hWcoordinate (k : Fin N) (a : Fin r) (i : Fin d) :
      W k (a, i) = ((K a - (envVector K (ψ k₀) a) • 1) *ᵥ ψ k) i := by
    simp only [W, Function.uncurry, Matrix.vecMulVec_apply, envVector, residualVector, PiLp.add_apply,
      WithLp.ofLp_toLp, PiLp.sub_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub, D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
      D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
      Matrix.vecMulVec_mulVec, op_smul_eq_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsum : (∑ a, ‖K a - (Matrix.trace (K a) / d) • 1‖ ^ 2) ≤
      B ^ 2 * ((N : ℝ) * (2 * ε + 2 * L * D)) := by
    calc
      _ ≤ ∑ a, B ^ 2 * ‖evaluationMap ψ (K a - (envVector K (ψ k₀) a) • 1)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        apply (centered_minimum hdpos (K a) _).trans
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
          (hb (K a - (envVector K (ψ k₀) a) • 1)) 2
      _ = B ^ 2 * ∑ k, ‖W k‖ ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [EuclideanSpace.norm_sq_eq, evaluationMap, Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro i _
        rw [hWcoordinate]
        rfl
      _ ≤ B ^ 2 * ((N : ℝ) * (2 * ε + 2 * L * D)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
        have hwSum : (∑ k : Fin N, ‖W k‖ ^ 2) ≤ ∑ k : Fin N, (2 * ε + 2 * L * D) :=
          Finset.sum_le_sum (fun k _ => hW k)
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hwSum
  have hεsqrt : ε ≤ Real.sqrt ε := by
    nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
  have hDsqrt : D ≤ 3 * Real.sqrt ε := by dsimp [D]; linarith
  rw [← hΦ, kraus_process_loss hdpos K hK, div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hdR).mpr
  have hh : 2 * ε + 2 * L * D ≤ (2 + 6 * L) * Real.sqrt ε := by nlinarith
  have hh2 : B ^ 2 * ((N : ℝ) * (2 * ε + 2 * L * D)) ≤
      B ^ 2 * (N + 1) * (2 + 6 * L) * Real.sqrt ε := by
    have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg B) (Nat.cast_nonneg N))
    nlinarith [mul_nonneg (sq_nonneg B) (mul_nonneg (by positivity : 0 ≤ 2 + 6 * L) (Real.sqrt_nonneg ε))]
  exact hsum.trans hh2
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
namespace D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
private theorem nonscalar_implies_sqrt {d N : ℕ} (ψ : Fin N → Fin d → ℂ) (hd : 2 ≤ d) (hψ : unitInputFamily ψ) (hspan : spanInputFamily ψ) (hconn : nonorthogonalityConnected ψ) (hS : ¬ scalarObstruction ψ) : SqrtScaling ψ := by
  have hdpos : 0 < d := Nat.zero_lt_of_lt hd
  obtain ⟨c, δ, hc, hδ, hl⟩ := nonscalar_sqrt_lower ψ hdpos hψ hS
  obtain ⟨C, hC, hu⟩ := general_channel_upper ψ hd hψ hspan hconn
  refine ⟨c, C, min δ 1, hc, hC, by positivity, ?_⟩
  intro ε hε hεδ
  have heδ : ε < δ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have he1 : ε < 1 := lt_of_lt_of_le hεδ (min_le_right _ _)
  refine ⟨hl ε hε heδ, ?_⟩
  apply f_upper_of_channels ψ ε (C * Real.sqrt ε)
  · exact ⟨LinearMap.id, identity_admissible ψ hψ ε hε.le⟩
  · exact hu ε hε he1
theorem result : claim := by
  intro d N ψ hd hψ hspan hconn
  have hlin := scalar_implies_linear ψ hd hψ
  have hsqrt := nonscalar_implies_sqrt ψ hd hψ hspan hconn
  constructor
  · constructor
    · exact hlin
    · intro hl
      by_contra hn
      exact scaling_exclusive ψ hl (hsqrt hn)
  · constructor
    · exact hsqrt
    · intro hs hn
      exact scaling_exclusive ψ (hlin hn) hs
end D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingTransition
