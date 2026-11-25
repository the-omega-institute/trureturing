import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.CenteredDisjointPrincipal

/-! Dependence of the principal coefficient remainder on the quadratic majorant. -/

namespace Reg.D5.S3.Fourier.Concentration.CenteredDisjointPrincipal

open Finset PowerSeries
open scoped ComplexConjugate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CenteredDisjointPrincipal
open _root_.D5.S3.Fourier.Concentration.DisjointCharacterEnvelope
open _root_.D5.S3.Fourier.Concentration.DisjointCharacterRemainder
open _root_.Reg.Support

noncomputable section
universe u

namespace Local

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ × ℝ × ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => quadraticBound x.1 x.2.1 x.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} (t : Finset J) (c : ℂ) (a : J → ℂ) (d : ℕ) (_ : t.card ≤ d),
    let n := d-t.card
    let u := c-(∑ j ∈ t, a j)/2
    let v := (∑ j ∈ t, ‖a j‖^2)/24
    let A := ∏ j ∈ t, ‖a j‖
    let readout := V.readout () ()
    let H := readout (‖u‖,v,n)
    let h := expTermNorm (‖u‖,n)
    ‖overlapCoefficient t c a d - principalTerm t c a d‖ ≤ A*(H-h) ∧
    |‖overlapCoefficient t c a d‖^2 - ‖principalTerm t c a d‖^2| ≤ A^2*(H^2-h^2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (J := ULift.{u} Unit) ∅ 0 (fun _ => 0) 0 (by simp)
  norm_num [rejected, realize, expTermNorm, principalTerm, overlapCoefficient,
    disjointSeries, axis_zero, Finset.filter_singleton] at hz

def evidence : Registration arena.{u} (type_of% @centered_principal_remainder.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@centered_principal_remainder.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0,0,1), (1,0,1), ?_⟩
    norm_num [actual, realize, quadraticBound, expTermNorm]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@centered_principal_remainder.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CenteredDisjointPrincipal.Local.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CenteredDisjointPrincipal.Local.evidence
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
    owner := `D5.S3.Fourier.Concentration.CenteredDisjointPrincipal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Local

namespace Mixed

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ × ℝ × ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => quadraticBound x.1 x.2.1 x.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} (s : Finset J) (a : J → ℂ) (d : ℕ),
    let c := ∑ j ∈ s, a j
    let admissible := s.powerset.filter (fun t => t.card ≤ d)
    let readout := V.readout () ()
    let H := fun t => readout (‖c-(∑ j ∈ t, a j)/2‖,
      (∑ j ∈ t, ‖a j‖^2)/24, d-t.card)
    let h := fun t => expTermNorm (‖c-(∑ j ∈ t, a j)/2‖,d-t.card)
    |(coeff d (coeff d (disjointSeries s a (fun j => conj (a j))))).re -
      ∑ t ∈ admissible, (-1 : ℝ)^t.card * ‖principalTerm t c a d‖^2| ≤
        ∑ t ∈ admissible, (∏ j ∈ t, ‖a j‖)^2 * (H t^2-h t^2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (J := ULift.{u} Unit) ∅ (fun _ => 0) 0
  norm_num [rejected, realize, expTermNorm, principalTerm, overlapCoefficient,
    disjointSeries, axis_zero, Finset.filter_singleton] at hz

def evidence : Registration arena.{u} (type_of% @mixed_centered_principal_error.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mixed_centered_principal_error.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0,0,1), (1,0,1), ?_⟩
    norm_num [actual, realize, quadraticBound, expTermNorm]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@mixed_centered_principal_error.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CenteredDisjointPrincipal.Mixed.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CenteredDisjointPrincipal.Mixed.evidence
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
    owner := `D5.S3.Fourier.Concentration.CenteredDisjointPrincipal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Mixed

end

end Reg.D5.S3.Fourier.Concentration.CenteredDisjointPrincipal
