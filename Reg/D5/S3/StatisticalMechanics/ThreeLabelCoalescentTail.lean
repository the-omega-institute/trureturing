import D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail
import Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent

/-! Source-bound registration of uniform tail positivity. -/
noncomputable section
namespace Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail
open _root_.D5.S3.StatisticalMechanics.ThreeLabelCoalescent
open _root_.D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent
open LeanInformationAudit

def tailArena : Arena where
  signature := determinantSignature
  Law R := ∃ U : Set (Fin 7 → ℝ), IsOpen U ∧ (∀ h, 0 < h → baseRates h ∈ U) ∧
    ∃ T : ℝ, 0 ≤ T ∧ ∀ r ∈ U, ∀ p : ℝ → Fin 5 → ℝ, GeneralForwardLaw r p →
      ∀ t, T ≤ t → 0 < R.readout () p t

private theorem rejected : ¬ tailArena.Law determinantRejected := by
  rintro ⟨U, _, hbase, T, _, hall⟩
  have hz := hall (baseRates 1) (hbase 1 (by norm_num)) (explicit 1) unitGeneral
    (max T 0) (le_max_left _ _)
  norm_num [determinantRejected, realize] at hz

def tailEvidence : Registration tailArena (type_of% uniform_positive_tail) where
  actual := determinantActual
  bridge := Iff.rfl
  variation := ⟨uniform_positive_tail, determinantRejected, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    tailArena.Law determinantActual determinantRejected rejected
  dependence := determinantDependence

def tailSelection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail
  definition := none
  coordinates := #[4]
  readouts := #[{
    path := #["arg", "body", "arg", "arg", "arg", "body", "arg",
      "body", "body", "body", "body", "body", "body", "arg"]
    stateBinder := 6
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

def tailRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@uniform_positive_tail) (Realization determinantSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail.tailUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail.tailEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena ⟨tailEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize determinantSignature determinantActual.readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some tailSelection
  continuation := .unknown
  familyRecord := none
  options := #[]

def nearArena : Arena where
  signature := determinantSignature
  Law R := ∀ (h : ℝ), 0 < h →
    ∃ U : Set (Fin 7 → ℝ), IsOpen U ∧ baseRates h ∈ U ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ U, ∀ p : ℝ → Fin 5 → ℝ, GeneralForwardLaw r p →
        ∀ t, 0 < t → t < ε → 0 < R.readout () p t

private theorem nearRejected : ¬ nearArena.Law determinantRejected := by
  intro hl
  obtain ⟨U, _, hbase, ε, hε, hall⟩ := hl 1 (by norm_num)
  have hz := hall (baseRates 1) hbase (explicit 1) unitGeneral (ε / 2) (by linarith) (by linarith)
  norm_num [determinantRejected, realize] at hz

def nearEvidence : Registration nearArena (type_of% uniform_positive_near_zero) where
  actual := determinantActual
  bridge := Iff.rfl
  variation := ⟨uniform_positive_near_zero, determinantRejected, nearRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    nearArena.Law determinantActual determinantRejected nearRejected
  dependence := determinantDependence

def nearSelection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail
  definition := none
  coordinates := #[6]
  readouts := #[{
    path := #["body", "body", "arg", "body", "arg", "arg", "arg", "body", "arg",
      "body", "body", "body", "body", "body", "body", "body", "arg"]
    stateBinder := 8
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

def nearRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@uniform_positive_near_zero) (Realization determinantSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail.nearUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail.nearEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨nearArena⟩
  objectArena := .source ⟨nearArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nearArena ⟨nearEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize determinantSignature determinantActual.readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some nearSelection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms nearRegistration
#print axioms tailRegistration
end Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail
