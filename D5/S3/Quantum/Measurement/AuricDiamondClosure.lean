import D5.S3.Quantum.Measurement.AuricExactDistance

/-! # Optimality in the unhalved diamond closure -/

namespace D5.S3.Quantum.Measurement.AuricDiamondClosure

open _root_.Matrix Filter D5.S3.Quantum.Foundation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Measurement.AuricExactDistance
open D5.S3.Quantum.Measurement.AuricFiveLevelReadout (inputVector)
open D5.S3.Quantum.Measurement.AuricFiveLevelTilt
open D5.S3.Quantum.Measurement.AuricSimulatorUpper
open scoped ComplexOrder MatrixOrder

/-- An unhalved diamond bound tested on every complex matrix with every finite reference. -/
def DiamondBound (F : RecordedMap) (bound : ℝ) : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R] (X : Matrix (Level × R) (Level × R) ℂ),
    FiniteTraceDistance.traceNorm (MatrixMap.kron F (LinearMap.id : MatrixMap R R ℂ) X) ≤
      bound * FiniteTraceDistance.traceNorm X

/-- Closure under the operational diamond norm, expressed by its positive-radius balls. -/
def ProtocolClosure (F : RecordedMap) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ G, FiniteProtocolMixture G ∧ DiamondBound (F - G) ε

private theorem amplified_sub {R : Type} [Fintype R] [DecidableEq R] (F G : RecordedMap)
    (X : Matrix (Level × R) (Level × R) ℂ) :
    MatrixMap.kron (F - G) (LinearMap.id : MatrixMap R R ℂ) X =
      MatrixMap.kron F (LinearMap.id : MatrixMap R R ℂ) X -
        MatrixMap.kron G (LinearMap.id : MatrixMap R R ℂ) X := by
  ext ⟨i, s⟩ ⟨j, t⟩
  simp only [MatrixMap.kron_def, LinearMap.sub_apply, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

private theorem traceNorm_zero {ι : Type} [Fintype ι] :
    FiniteTraceDistance.traceNorm (0 : Matrix ι ι ℂ) = 0 := by
  simp [FiniteTraceDistance.traceNorm]

private theorem diamondBound_zero {ε : ℝ} (hε : 0 ≤ ε) : DiamondBound 0 ε := by
  intro R _ _ X
  have hzero : MatrixMap.kron (0 : RecordedMap) (LinearMap.id : MatrixMap R R ℂ) X = 0 := by
    ext ⟨i, s⟩ ⟨j, t⟩
    simp [MatrixMap.kron_def]
  rw [hzero, traceNorm_zero]
  exact mul_nonneg hε (FiniteTraceDistance.traceNorm_nonneg X)

theorem FiniteProtocolMixture.inClosure {F : RecordedMap} (hF : FiniteProtocolMixture F) :
    ProtocolClosure F := by
  intro ε hε
  exact ⟨F, hF, by rw [sub_self]; exact diamondBound_zero hε.le⟩

private theorem witness_norm (r : WitnessInterval) :
    FiniteTraceDistance.traceNorm (vecMulVec (inputVector r) (star (inputVector r))) = 1 := by
  let ρ := vecMulVec (inputVector r) (star (inputVector r))
  change FiniteTraceDistance.traceNorm ρ = 1
  have hp : ρ.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have hr0 : (0 : ℝ) < r := by linarith [r.property.1]
  have ht := D5.S3.Quantum.Measurement.AuricFiveLevelReadout.input_purification_trace r hr0
  unfold FiniteTraceDistance.traceNorm
  rw [hp.1.eq, ← pow_two, CFC.sqrt_sq ρ]
  exact congrArg Complex.re ht

set_option maxHeartbeats 1000000 in
/-- The same fixed normalized witness gives the lower bound for every limit of
finite randomized protocols, without any bound on the depths of its approximants. -/
theorem matching_lower_bound_in_closure (r : WitnessInterval)
    (hr : matchingResidual r (tiltMass r) = 0) (F : RecordedMap) (hF : ProtocolClosure F) :
    2 * matchingWeight r ≤ FiniteTraceDistance.traceNorm
      (MatrixMap.kron (target - F) (LinearMap.id : MatrixMap Level Level ℂ)
        (vecMulVec (inputVector r) (star (inputVector r)))) := by
  let ρ := vecMulVec (inputVector r) (star (inputVector r))
  have hρ : FiniteTraceDistance.traceNorm ρ = 1 := witness_norm r
  let lift (A : RecordedMap) := MatrixMap.kron A (LinearMap.id : MatrixMap Level Level ℂ) ρ
  change 2 * matchingWeight r ≤ FiniteTraceDistance.traceNorm (lift (target - F))
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨G, hG, hεG⟩ := hF ε hε
  have htri := FiniteTraceDistance.traceNorm_add_le (lift (target - F)) (lift (F - G))
  have he : lift (target - F) + lift (F - G) = lift (target - G) := calc
    _ = (lift target - lift F) + (lift F - lift G) :=
      congrArg₂ (· + ·) (amplified_sub target F ρ) (amplified_sub F G ρ)
    _ = lift target - lift G := sub_add_sub_cancel _ _ _
    _ = _ := (amplified_sub target G ρ).symm
  rw [he] at htri
  have hnear := hεG Level ρ
  change FiniteTraceDistance.traceNorm (lift (F - G)) ≤ ε * FiniteTraceDistance.traceNorm ρ at hnear
  rw [hρ, mul_one] at hnear
  have hlo := matching_lower_bound r hr G hG
  change 2 * matchingWeight r ≤ FiniteTraceDistance.traceNorm (lift (target - G)) at hlo
  have hsum : FiniteTraceDistance.traceNorm (lift (target - F)) +
      FiniteTraceDistance.traceNorm (lift (F - G)) ≤
        FiniteTraceDistance.traceNorm (lift (target - F)) + ε :=
    add_le_add (le_refl (FiniteTraceDistance.traceNorm (lift (target - F)))) hnear
  exact le_trans hlo (le_trans htri hsum)

/-- The unhalved diamond distance to the entire closure has a minimum. A finite
input-independent randomized protocol already attains it. -/
theorem exact_distance_to_protocol_closure :
    ∃ r : WitnessInterval, matchingResidual r (tiltMass r) = 0 ∧
      FiniteProtocolMixture (matchingSimulator r) ∧
      DiamondBound (target - matchingSimulator r) (2 * matchingWeight r) ∧
      IsLeast {d : ℝ | ∃ F, ProtocolClosure F ∧ DiamondBound (target - F) d}
        (2 * matchingWeight r) := by
  obtain ⟨r, hr, hfinite, _, _, hupper⟩ := exact_finite_protocol_distance
  have hmatch : DiamondBound (target - matchingSimulator r) (2 * matchingWeight r) := hupper
  refine ⟨r, hr, hfinite, hmatch,
    ⟨⟨matchingSimulator r, FiniteProtocolMixture.inClosure hfinite, hmatch⟩, ?_⟩⟩
  rintro d ⟨F, hF, hbound⟩
  let ρ := vecMulVec (inputVector r) (star (inputVector r))
  have hρ : FiniteTraceDistance.traceNorm ρ = 1 := witness_norm r
  calc
    _ ≤ FiniteTraceDistance.traceNorm
        (MatrixMap.kron (target - F) (LinearMap.id : MatrixMap Level Level ℂ) ρ) :=
      matching_lower_bound_in_closure r hr F hF
    _ ≤ d := by simpa only [hρ, mul_one] using hbound Level ρ

end D5.S3.Quantum.Measurement.AuricDiamondClosure
