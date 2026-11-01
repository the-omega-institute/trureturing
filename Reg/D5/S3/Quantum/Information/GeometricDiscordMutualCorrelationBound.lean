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


namespace RotatedSpin

open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (vlen)

abbrev signature :=
  _root_.Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.signature

def actual : Realization signature :=
  realize signature (fun _ _ ρ => maximalMutualCorrelation ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : TwoQubit), ρ.PosSemidef → trace ρ = 1 →
    ∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) (c d : Fin 3 → ℝ),
      vlen c = 1 → vlen d = 1 →
        |c ⬝ᵥ (connectedCorrelation (rotateState U ρ) *ᵥ d)| ≤ R.readout () () ρ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : vlen ![1, 0, 0] = 1 := by norm_num [vlen, Fin.sum_univ_three]
  have hb := h mixedState mixedState_positive mixedState_trace 1 ![1, 0, 0] ![1, 0, 0] he he
  let q : ℝ := (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ
    (connectedCorrelation (rotateState 1 mixedState) *ᵥ ![1, 0, 0])
  have hb' : |q| ≤ -1 := hb
  linarith [abs_nonneg q]

def source_registration : Registration arena (type_of% @rotated_spin_witness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rotated_spin_witness, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence :=
    _root_.Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rotated_spin_witness) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.RotatedSpin.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.RotatedSpin
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => maximalMutualCorrelation ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end RotatedSpin

namespace MarginalBasis

open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (blochA pauli pauli_zero)

abbrev signature : Signature where
  Params := Unit
  State _ := TwoQubit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 3 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ρ => blochA ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : TwoQubit), ρ.PosSemidef →
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      R.readout () () (rotateState U ρ) 0 = 0 ∧
        blochA (rotateState U ρ) 1 = 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨U, hU, _⟩ := h 0 Matrix.PosSemidef.zero
  norm_num [rejected, realize] at hU

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, (pauli 0 ⊗ₖ (1 : Qubit)), ?_⟩
  change blochA (0 : TwoQubit) ≠ blochA (pauli 0 ⊗ₖ (1 : Qubit))
  intro he
  have h0 := congrFun he 0
  norm_num [blochA, pauli_zero, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two] at h0

def source_registration : Registration arena (type_of% @marginal_basis) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨marginal_basis, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@marginal_basis) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.MarginalBasis.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.MarginalBasis
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => blochA ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end MarginalBasis

end
end Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound

namespace Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.DensityExpectation

open _root_.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe the complex norm at the density expectation. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain every finite index type, both matrices, and both density hypotheses. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (ρ X : Matrix n n ℂ), ρ.PosSemidef → trace ρ = 1 →
      R.readout () () (trace (ρ * X)) ≤ ‖X‖

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := h (n := ULift.{u} Unit) 1 0 Matrix.PosSemidef.one (by simp)
  change (1 : ℝ) ≤ ‖(0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)‖ at hbad
  norm_num only [norm_zero] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num

def source_registration :
    Registration arena.{u} (type_of% @density_expectation_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨density_expectation_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@density_expectation_bound.{u}) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.DensityExpectation.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.DensityExpectation
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print density_expectation_bound
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.DensityExpectation
