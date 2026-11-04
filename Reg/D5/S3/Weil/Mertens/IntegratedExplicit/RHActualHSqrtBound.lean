import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound
import Reg.Support.SingleDependentReadout

/-! A source-bound registration for the conditional square-root envelope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ y => actualH y)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ y => actualH y + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    R.readout () () 0 = actualH 0 ∧
      ∀ hRH : RiemannHypothesis, ∀ y : ℝ,
        ‖R.readout () () y‖ ≤
          (101 / 100 : ℝ) * firstLiMass * Real.exp (y / 2)

private theorem actual_law : arena.Law actual := by
  constructor
  · rfl
  · intro hRH y
    change ‖actualH y‖ ≤
      (101 / 100 : ℝ) * firstLiMass * Real.exp (y / 2)
    exact (actualH_sqrt_bound_of_rh_registered.2 hRH y)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨heq, _⟩
  change actualH 0 + 1 = actualH 0 at heq
  have hz : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = (actualH 0 + 1) - actualH 0 := by ring
      _ = 0 := sub_eq_zero.mpr heq
  exact one_ne_zero hz

private theorem actual_dependence :
    ObservationalDependence signature actual := by
  intro i
  obtain ⟨y, hy⟩ := _root_.D5.S3.Weil.Mertens.IntegratedExplicit.actualH_nonconstant
  refine ⟨(), (0 : ℝ), y, ?_⟩
  change actualH 0 ≠ actualH y
  exact hy.symm

def nonconstantRejected : Realization signature :=
  realize signature (fun _ _ _ => actualH 0)
    (fun e => nomatch e)

abbrev nonconstantArena : Arena where
  signature := signature
  Law R := ∃ y : ℝ, R.readout () () y ≠ R.readout () () 0

theorem nonconstant_rejected_law : ¬ nonconstantArena.Law nonconstantRejected := by
  rintro ⟨y, hy⟩
  change actualH 0 ≠ actualH 0 at hy
  exact hy rfl

def nonconstantEvidence : Registration nonconstantArena
    (type_of% @actualH_nonconstant) where
  actual := actual
  bridge := by
    constructor
    · intro h
      obtain ⟨y, hy⟩ := h
      change actualH y ≠ actualH 0 at hy
      exact ⟨y, hy⟩
    · intro h
      obtain ⟨y, hy⟩ := h
      refine ⟨y, ?_⟩
      change actualH y ≠ actualH 0 at hy
      exact hy
  variation := ⟨actualH_nonconstant, nonconstantRejected, nonconstant_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    nonconstantArena.Law actual nonconstantRejected nonconstant_rejected_law
  dependence := actual_dependence

def nonconstantRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actualH_nonconstant) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound.actualH_nonconstant.__information_unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound.nonconstantEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨nonconstantArena⟩
  objectArena := .source ⟨nonconstantArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nonconstantArena ⟨nonconstantEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def evidence : Registration arena (type_of% @actualH_sqrt_bound_of_rh_registered) where
  actual := actual
  bridge := by
    constructor
    · intro h
      exact h
    · intro h
      exact h
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actualH_sqrt_bound_of_rh_registered) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound.actualH_sqrt_bound_of_rh_registered.__information_unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound
