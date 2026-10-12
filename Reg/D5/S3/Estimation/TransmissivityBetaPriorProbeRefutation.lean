import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder
open D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (outputState)
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation
noncomputable section

private theorem unit_density (τ : ℝ) : betaDensity 1 1 τ = 1 := by
  have g2 : Real.Gamma 2 = 1 := by
    convert Real.Gamma_nat_eq_factorial 1 using 1 <;> norm_num
  norm_num [betaDensity, Real.Gamma_one, g2]

private theorem unit_density_continuous :
    ContinuousOn (betaDensity 1 1) (Set.Icc 0 1) := by
  have eq : betaDensity 1 1 = fun _ => 1 := funext unit_density
  rw [eq]
  exact continuous_const.continuousOn

private def vacuum : Fin 1 → ℂ := fun _ => 1

private theorem vacuum_output (τ : ℝ) : outputState τ vacuum = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  norm_num [outputState, vacuum, amplitudeKraus, rankOneDensity,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
    vecMulVec, Pi.star_apply]

private theorem vacuum_matrix_risk (b : ℝ) :
    deltaBMatrix 1 1 vacuum ((b : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) =
      b ^ 2 - b + 1 / 3 := by
  unfold deltaBMatrix
  have integrand (τ : ℝ) : betaDensity 1 1 τ *
      ((outputState τ vacuum *
        ((b : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) - (τ : ℂ) • 1) ^ 2).trace).re =
      b ^ 2 - (2 * b) * τ + τ ^ 2 := by
    rw [unit_density, vacuum_output]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.sub_apply, pow_two, Fin.sum_univ_succ, Complex.mul_re, Complex.sub_re]
    <;> ring
  simp_rw [integrand]
  have hc : IntervalIntegrable (fun _ : ℝ => b ^ 2) volume 0 1 :=
    intervalIntegrable_const
  have hm : IntervalIntegrable (fun τ : ℝ => (2 * b) * τ) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hp : IntervalIntegrable (fun τ : ℝ => τ ^ 2) volume 0 1 :=
    (continuous_id.pow 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add (hc.sub hm) hp,
    intervalIntegral.integral_sub hc hm, intervalIntegral.integral_const_mul]
  norm_num [integral_pow, integral_id, intervalIntegral.integral_const]
  ring

private theorem vacuum_zero_risk :
    deltaB 1 1 vacuum (0 : FockSpace →L[ℂ] FockSpace) = 1 / 3 := by
  unfold deltaB
  have integrand (τ : ℝ) : betaDensity 1 1 τ *
      (∑ i, ∑ j, outputState τ vacuum i j * inner ℂ (e j)
        ((((0 : FockSpace →L[ℂ] FockSpace) - τ • 1) * (0 - τ • 1)) (e i))).re =
      τ ^ 2 := by
    rw [unit_density, vacuum_output]
    simp [Fin.sum_univ_succ, ContinuousLinearMap.mul_apply, _root_.sub_apply,
      _root_.smul_apply, one_apply_eq_self, inner_smul_right, e,
      lp.inner_single_left, RCLike.inner_apply, lp.single_apply, Pi.single_apply,
      Complex.mul_re, pow_two]
  simp_rw [integrand]
  norm_num [integral_pow]

abbrev momentSignature : Signature where
  Params := Σ N : ℕ, Σ _α : ℝ, Σ _β : ℝ, (Fin (N + 1) → ℂ)
  State p := Matrix (Fin (p.1 + 1)) (Fin (p.1 + 1)) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def momentActual : Realization momentSignature :=
  realize momentSignature (fun _ p H => deltaBMatrix p.2.1 p.2.2.1 p.2.2.2 H)
    (fun e => nomatch e)

def momentRejected : Realization momentSignature :=
  realize momentSignature (fun _ p H => deltaBMatrix p.2.1 p.2.2.1 p.2.2.2 H + 1)
    (fun e => nomatch e)

abbrev momentArena : Arena where
  signature := momentSignature
  Law R := ∀ {N : ℕ} (α β : ℝ) (ψ : Fin (N + 1) → ℂ)
      (H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
      (_hp : ContinuousOn (betaDensity α β) (Set.Icc 0 1)),
    R.readout () ⟨N, α, β, ψ⟩ H = ((H * H * momentBeta α β ψ 0).trace -
      2 * (H * momentBeta α β ψ 1).trace + (momentBeta α β ψ 2).trace).re

private theorem moment_rejected_law : ¬ momentArena.Law momentRejected := by
  intro h
  have bad := @h 0 1 1 vacuum 0 unit_density_continuous
  have good := deltaBMatrix_eq_moments 1 1 vacuum 0 unit_density_continuous
  change deltaBMatrix 1 1 vacuum 0 + 1 = _ at bad
  linarith

def momentProof : Registration momentArena (type_of% (@deltaBMatrix_eq_moments)) where
  actual := momentActual
  bridge := Iff.rfl
  variation := ⟨@deltaBMatrix_eq_moments, momentRejected, moment_rejected_law⟩
  sensitivity := ⟨fun i => ⟨momentRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, moment_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0, 1, 1, vacuum⟩, (0 : ℂ) • 1, (2 : ℂ) • 1, ?_⟩
    change deltaBMatrix 1 1 vacuum ((0 : ℂ) • 1) ≠
      deltaBMatrix 1 1 vacuum ((2 : ℂ) • 1)
    have risk0 := vacuum_matrix_risk 0
    have risk2 := vacuum_matrix_risk 2
    norm_num at risk0 risk2
    simp only [zero_smul]
    rw [risk0, risk2]
    norm_num

abbrev compressionSignature : Signature where
  Params := ℕ
  State _ := FockSpace →L[ℂ] FockSpace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ N := Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def compressionActual : Realization compressionSignature :=
  realize compressionSignature (fun _ N H => compression (N := N) H)
    (fun e => nomatch e)

def compressionRejected : Realization compressionSignature :=
  realize compressionSignature (fun _ _ _ => (2 : ℂ) • 1) (fun e => nomatch e)

abbrev compressionArena : Arena where
  signature := compressionSignature
  Law R := ∀ {N : ℕ} (α β : ℝ) (ψ : Fin (N + 1) → ℂ)
      (H : FockSpace →L[ℂ] FockSpace) (_hH : IsSelfAdjoint H)
      (_hp : ContinuousOn (betaDensity α β) (Set.Icc 0 1))
      (_hn : ∀ τ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ betaDensity α β τ)
      (_hρ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (outputState τ ψ).PosSemidef),
    deltaBMatrix α β ψ (R.readout () N H) ≤ deltaB α β ψ H

private theorem compression_rejected_law : ¬ compressionArena.Law compressionRejected := by
  intro h
  have hn : ∀ τ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ betaDensity 1 1 τ := by
    intro τ _
    rw [unit_density]
    norm_num
  have hρ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (outputState τ vacuum).PosSemidef := by
    intro τ _
    rw [vacuum_output]
    exact Matrix.PosSemidef.one
  have bad := @h 0 1 1 vacuum 0 (IsSelfAdjoint.zero _) unit_density_continuous hn hρ
  change deltaBMatrix 1 1 vacuum ((2 : ℂ) • 1) ≤ deltaB 1 1 vacuum 0 at bad
  have risk2 := vacuum_matrix_risk 2
  norm_num at risk2
  rw [risk2, vacuum_zero_risk] at bad
  norm_num at bad

def compressionProof : Registration compressionArena (type_of% (@compression_le)) where
  actual := compressionActual
  bridge := Iff.rfl
  variation := ⟨@compression_le, compressionRejected, compression_rejected_law⟩
  sensitivity := ⟨fun i => ⟨compressionRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, compression_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    intro equality
    have impossible := congrFun (congrFun equality 0) 0
    norm_num [compressionActual, realize, compression, e, lp.inner_single_left,
      RCLike.inner_apply, lp.single_apply, Pi.single_apply] at impossible

def deltaBMatrix_eq_moments_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.deltaBMatrix_eq_moments)
    (Realization momentSignature) (Type) (Unit) where
  unitName := `Reg.D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.deltaBMatrix_eq_moments
  realizationName := `Reg.D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.momentProof
  realizationSource := none
  generated := false
  arena := .source ⟨momentArena⟩
  objectArena := .source ⟨momentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source momentArena ⟨momentProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature momentActual.readout momentActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms momentProof
#print axioms deltaBMatrix_eq_moments_registration

def compression_le_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.compression_le)
    (Realization compressionSignature) (Type) (Unit) where
  unitName := `Reg.D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.compression_le
  realizationName := `Reg.D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.compressionProof
  realizationSource := none
  generated := false
  arena := .source ⟨compressionArena⟩
  objectArena := .source ⟨compressionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source compressionArena ⟨compressionProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize compressionSignature compressionActual.readout compressionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms compressionProof
#print axioms compression_le_registration

end
end Reg.D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation
