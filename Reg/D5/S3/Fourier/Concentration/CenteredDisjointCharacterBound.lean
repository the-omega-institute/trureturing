import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.CenteredDisjointCharacterBound

/-! The centered coefficient bound depends on the factorial coefficient readout. -/

namespace Reg.D5.S3.Fourier.Concentration.CenteredDisjointCharacterBound

open Finset PowerSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CenteredDisjointCharacterBound
open _root_.D5.S3.Fourier.Concentration.DisjointCharacterEnvelope
open _root_.D5.S3.Fourier.Concentration.DisjointCharacterRemainder
open _root_.Reg.Support

noncomputable section
universe u

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ × ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => expTermNorm) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} (t : Finset J) (c : ℂ) (a : J → ℂ) (d : ℕ),
    let k := t.card
    let u := c - (∑ j ∈ t, a j)/2
    let v := (∑ j ∈ t, ‖a j‖^2)/24
    let term := V.readout () ()
    ‖overlapCoefficient t c a d‖ ≤
      if k ≤ d then (∏ j ∈ t, ‖a j‖) *
        (∑ m ∈ range ((d-k)/2+1), term (‖u‖, d-k-2*m) * term (v, m)) else 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (J := ULift.{u} Unit) ∅ 0 (fun _ => 0) 0
  norm_num [rejected, realize, overlapCoefficient, axis_zero] at hz

def evidence : Registration arena.{u} (type_of% @centered_overlap_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@centered_overlap_bound.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0,1), (1,1), ?_⟩
    norm_num [actual, realize, expTermNorm]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@centered_overlap_bound.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CenteredDisjointCharacterBound.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CenteredDisjointCharacterBound.evidence
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
    owner := `D5.S3.Fourier.Concentration.CenteredDisjointCharacterBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CenteredDisjointCharacterBound
