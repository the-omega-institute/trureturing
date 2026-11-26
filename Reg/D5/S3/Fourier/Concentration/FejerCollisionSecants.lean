import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.FejerCollisionSecants

/-! Source dependence of positive-part collision increments. -/

namespace Reg.D5.S3.Fourier.Concentration.FejerCollisionSecants

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FejerCollisionSecants
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open _root_.Reg.Support

noncomputable section
universe u

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => max 0 (z.1-z.2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0,0), (1,0), ?_⟩
  norm_num [actual,realize]

namespace Secants

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} (s : Finset I) (x c : I → ℝ),
    (∀ i ∈ s, ∀ j ∈ s, 0 ≤ c i*c j) → ∀ (r : ℝ) {δ : ℝ}, 0 < δ →
    let ramp := R.readout () ()
    let L := fun t => ∑ i ∈ s, ∑ j ∈ s, c i*c j*ramp (t,|x i-x j|)
    L r-L (r-δ) ≤ δ*nearCollisionMass s x c r ∧
      δ*nearCollisionMass s x c r ≤ L (r+δ)-L r

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  let i := ULift.up.{u} ()
  have hz := (law {i} (fun _ => 0) (fun _ => 1)
    (fun _ _ _ _ => by norm_num) 1 (δ := 1) zero_lt_one).2
  norm_num [rejected,realize,nearCollisionMass] at hz

def evidence : Registration arena.{u} (type_of% @collision_ramp_secants.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@collision_ramp_secants.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@collision_ramp_secants.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionSecants.Secants.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionSecants.Secants.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FejerCollisionSecants
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Secants

namespace ExactRight

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} (s : Finset I) (x c : I → ℝ) (r : ℝ),
    let ramp := R.readout () ()
    let L := fun t => ∑ i ∈ s, ∑ j ∈ s, c i*c j*ramp (t,|x i-x j|)
    (∀ δ : ℝ, 0 < δ → (∀ i ∈ s, ∀ j ∈ s, |x i-x j|≤r ∨ r+δ≤|x i-x j|) →
      L (r+δ)-L r = δ*nearCollisionMass s x c r) ∧
    (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      L (r+δ)-L r = δ*nearCollisionMass s x c r)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  let i := ULift.up.{u} ()
  obtain ⟨δ₀,hδ₀,h⟩ := (law {i} (fun _ => 0) (fun _ => 1) 1).2
  have he := h δ₀ hδ₀ le_rfl
  have hz : (0:ℝ) = δ₀ := by
    simpa [rejected,realize,nearCollisionMass] using he
  linarith

def evidence : Registration arena.{u} (type_of% @collision_ramp_exact_right.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@collision_ramp_exact_right.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@collision_ramp_exact_right.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionSecants.ExactRight.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionSecants.ExactRight.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FejerCollisionSecants
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExactRight

end

end Reg.D5.S3.Fourier.Concentration.FejerCollisionSecants
