import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Decoherence.FourLevelBathCubic
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Decoherence.FourLevelBathCubic

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Decoherence.FourLevelBathPhysical
open _root_.D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic
open _root_.D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics (projectiveReadout)
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open _root_.D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation (IsEnergyConserving)
open _root_.D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation (operation)
open GibbsBathBandwidth (gibbsWeight)

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => Bath → ℝ) (fun _ => Prop)

/-- Observe the existence of one permitted unitary pinching every density input. -/
def actual : Realization signature :=
  realize signature (fun _ β E =>
    ∃ U : Matrix.unitaryGroup (System × Bath) ℂ,
      IsEnergyConserving (fun _ => 0) E (U : Joint) ∧
      ∀ ρ : DensityState System,
        operation β E (U : Joint) (inputMatrix ρ) = projectiveReadout (inputMatrix ρ))
    (fun e => nomatch e)

/-- Intervene by reporting only the cap at the same prescribed law. -/
def capOnly : Realization signature :=
  realize signature (fun _ β E => ∀ b, gibbsWeight β E b ≤ 1 / 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (β : ℝ) (E : Bath → ℝ) (_hE : Function.Injective E),
    R.readout () β E ↔
      let p := gibbsWeight β E
      (∀ b, p b ≤ 1 / 3) ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        (∀ b, q p b ^ 2 * t ≥ d p b ^ 2) ∧ phaseCubic p t = 0

private theorem capOnly_fails : ¬ arena.Law capOnly := by
  intro h
  obtain ⟨E, hE, _, hcap, hno⟩ := infeasible_fixed_bath_example 1 (by norm_num)
  have hread : capOnly.readout () 1 E := fun b => (hcap b).le
  exact hno ((fixed_bath_pinching_iff_cubic 1 E hE).2 ((h 1 E hE).1 hread))

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  obtain ⟨Egood, _, _, hgood⟩ := feasible_fixed_bath_example 1 (by norm_num)
  obtain ⟨Ebad, _, _, _, hbad⟩ := infeasible_fixed_bath_example 1 (by norm_num)
  refine ⟨1, Egood, Ebad, ?_⟩
  intro heq
  exact hbad (Eq.mp heq hgood)

def source_registration : Registration arena (type_of% @fixed_bath_pinching_iff_cubic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_bath_pinching_iff_cubic, capOnly, capOnly_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual capOnly
    capOnly_fails
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixed_bath_pinching_iff_cubic) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Decoherence.FourLevelBathCubic.unit
  realizationName := `Reg.D5.S3.Quantum.Decoherence.FourLevelBathCubic.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ β E =>
    ∃ U : Matrix.unitaryGroup (System × Bath) ℂ,
      IsEnergyConserving (fun _ => 0) E (U : Joint) ∧
      ∀ ρ : DensityState System,
        operation β E (U : Joint) (inputMatrix ρ) = projectiveReadout (inputMatrix ρ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Decoherence.FourLevelBathCubic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Decoherence.FourLevelBathCubic
