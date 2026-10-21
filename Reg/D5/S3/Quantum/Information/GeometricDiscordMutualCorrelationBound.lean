import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the geometric-discord lower bound on mutual correlation. -/

namespace Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound

open _root_.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Kronecker ComplexOrder Matrix.Norms.L2Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

local notation "Qubit" => Matrix (Fin 2) (Fin 2) ℂ
local notation "TwoQubit" => Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Observe maximal mutual correlation as the two-qubit matrix varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := TwoQubit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ρ => maximalMutualCorrelation ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Retain both density hypotheses and the complete discord-correlation inequality. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ ρ : TwoQubit, ρ.PosSemidef → trace ρ = 1 →
    Real.sqrt (geometricDiscord ρ) ≤ r.readout () () ρ

private def mixedState : TwoQubit := (1 / 4 : ℝ) • 1

private theorem mixedState_positive : mixedState.PosSemidef :=
  PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 4)

private theorem mixedState_trace : trace mixedState = 1 := by
  norm_num [mixedState, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h mixedState mixedState_positive mixedState_trace
  change Real.sqrt (geometricDiscord mixedState) ≤ -1 at hbad
  linarith [Real.sqrt_nonneg (geometricDiscord mixedState)]

private theorem correlation_bounded (ρ : TwoQubit) :
    BddAbove {r | ∃ a b : Qubit, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      r = ‖localCovariance ρ a b‖} := by
  have hc : Continuous (fun p : Qubit × Qubit => ‖localCovariance ρ p.1 p.2‖) := by
    simp only [localCovariance, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.kroneckerMap_apply]
    fun_prop
  obtain ⟨K, hK⟩ := ((isCompact_sphere (0 : Qubit) 1).prod
    (isCompact_sphere (0 : Qubit) 1)).bddAbove_image hc.continuousOn
  refine ⟨K, ?_⟩
  rintro r ⟨a, b, ha, hb, rfl⟩
  apply hK
  exact ⟨(a, b), ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using ha,
    by simpa only [Metric.mem_sphere, dist_zero_right] using hb⟩, rfl⟩

private theorem correlation_zero : maximalMutualCorrelation 0 = 0 := by
  have hs : {r : ℝ | ∃ a b : Qubit, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      r = ‖localCovariance 0 a b‖} = {0} := by
    ext r
    constructor
    · rintro ⟨a, b, _, _, hr⟩
      simpa [localCovariance] using hr
    · intro hr
      refine ⟨1, 1, norm_one, norm_one, ?_⟩
      simpa [localCovariance] using Set.mem_singleton_iff.mp hr
  rw [maximalMutualCorrelation, hs, csSup_singleton]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  have hvalue : ‖localCovariance (1 : TwoQubit) (1 : Qubit) (1 : Qubit)‖ = 12 := by
    norm_num [localCovariance, one_kronecker_one, Matrix.trace, Matrix.diag,
      Fintype.sum_prod_type, Fin.sum_univ_two]
  have hbound : 12 ≤ maximalMutualCorrelation (1 : TwoQubit) := by
    rw [← hvalue]
    exact le_csSup (correlation_bounded 1) ⟨1, 1, norm_one, norm_one, rfl⟩
  change maximalMutualCorrelation 0 ≠ maximalMutualCorrelation 1
  rw [correlation_zero]
  linarith

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ ρ => maximalMutualCorrelation ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
    definition := some {
      owner := `D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
      name := `D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
