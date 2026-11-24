import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.DegreeTwoMomentWitness

/-! Dependence of the finite witness on the shared second moment. -/

namespace Reg.D5.S3.Fourier.Concentration.DegreeTwoMomentWitness

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (nearCollisionMass)
open _root_.D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy (degreeTwoResidualMass)
open _root_.D5.S3.Fourier.Concentration.DegreeTwoMomentWitness
open _root_.Reg.Support

noncomputable section

abbrev signature := SingleDependentReadout.signature Unit (fun _ => Fin 5 → ℤ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ g => ∑ i, g i ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V :=
    let secondMoment := fun g : Fin 5 → ℤ => V.readout () () g
    ∃ a b : Fin 5 → ℤ,
      (∑ i, a i) = 25 ∧ (∑ i, b i) = 25 ∧
      secondMoment a = 231 ∧ secondMoment b = 231 ∧
      (∀ i, a i ∈ Set.Icc 0 13 ∧ b i ∈ Set.Icc 0 13) ∧
      a 0 = 0 ∧ b 0 = 0 ∧ a 4 = 13 ∧ b 4 = 13 ∧
      ∀ η : ℝ, 0 ≤ η → η < 1 →
        nearCollisionMass univ (fun i => (a i : ℝ)) (fun _ => 1) η = 5 ∧
        nearCollisionMass univ (fun i => (b i : ℝ)) (fun _ => 1) η = 5 ∧
        degreeTwoResidualMass (fun i => (a i : ℝ)) (fun _ => 1) η = 8 ∧
        degreeTwoResidualMass (fun i => (b i : ℝ)) (fun _ => 1) η = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨a, b, ha, hb, hsecond, _⟩
  norm_num [rejected, realize] at hsecond

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def evidence : Registration arena (type_of% @exists_equal_first_data_distinct_degree_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_equal_first_data_distinct_degree_two, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_equal_first_data_distinct_degree_two) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.DegreeTwoMomentWitness.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.DegreeTwoMomentWitness.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ g => ∑ i, g i ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.DegreeTwoMomentWitness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.DegreeTwoMomentWitness
