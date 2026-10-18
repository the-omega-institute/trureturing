import D5.S3.StatisticalMechanics.ThreeLabelCoalescentPerturbation
import Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent

/-! Source-bound registration of seven-rate crossing stability. -/
noncomputable section
namespace Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescentPerturbation
open _root_.D5.S3.StatisticalMechanics.ThreeLabelCoalescent
open _root_.D5.S3.StatisticalMechanics.ThreeLabelCoalescentPerturbation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent
open LeanInformationAudit

def stabilityArena : Arena where
  signature := determinantSignature
  Law R := ∀ (h : ℝ), 0 < h → TwoCrossings h →
    ∃ U : Set (Fin 7 → ℝ), IsOpen U ∧ baseRates h ∈ U ∧
      (∀ r ∈ U, ∀ i, 0 < r i) ∧
      ∀ r ∈ U, ∀ p : ℝ → Fin 5 → ℝ, GeneralForwardLaw r p →
        TwoSimpleCrossings (fun t => R.readout () p t)

private theorem rejected : ¬ stabilityArena.Law determinantRejected := by
  intro hl
  obtain ⟨hc, τc, hhc, _, _, _, _, _, low, _, _⟩ := unique_fold_classification
  obtain ⟨U, _, hr, _, hall⟩ := hl 1 (by norm_num) (low 1 (by norm_num) hhc.1)
  have hz := hall (baseRates 1) hr (explicit 1) unitGeneral
  obtain ⟨a, b, _, _, _, _, hda, _⟩ := hz
  simpa [determinantRejected, realize] using hda

def stabilityEvidence : Registration stabilityArena (type_of% seven_rate_two_crossings_stable) where
  actual := determinantActual
  bridge := Iff.rfl
  variation := ⟨seven_rate_two_crossings_stable, determinantRejected, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    stabilityArena.Law determinantActual determinantRejected rejected
  dependence := determinantDependence

def stabilitySelection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.ThreeLabelCoalescentPerturbation
  definition := none
  coordinates := #[6]
  readouts := #[{
    path := #["body", "body", "body", "arg", "body", "arg", "arg", "arg",
      "body", "body", "body", "body", "arg", "body"]
    stateBinder := 8
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

def stabilityRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@seven_rate_two_crossings_stable) (Realization determinantSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescentPerturbation.stabilityUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescentPerturbation.stabilityEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨stabilityArena⟩
  objectArena := .source ⟨stabilityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stabilityArena ⟨stabilityEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize determinantSignature determinantActual.readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some stabilitySelection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms stabilityRegistration
end Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescentPerturbation
