import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.DisjointCharacterRemainder

/-! The signed coefficient estimates depend on the magnitude of each overlap amplitude. -/

namespace Reg.D5.S3.Fourier.Concentration.DisjointCharacterRemainder

open Finset PowerSeries
open scoped PowerSeries ComplexConjugate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.DisjointCharacterRemainder
open _root_.D5.S3.Fourier.Concentration.DisjointCharacterEnvelope
open _root_.Reg.Support

noncomputable section
universe u

namespace Expansion

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => fun z : ℂ => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} (s : Finset J) (a : J → ℂ) (d : ℕ),
    let c := ∑ j ∈ s, a j
    let magnitude := V.readout () ()
    coeff d (coeff d (disjointSeries s a (fun j => conj (a j)))) =
      ((∑ t ∈ s.powerset.filter (fun t => t.card ≤ d),
        (-1 : ℝ) ^ t.card * magnitude (overlapCoefficient t c a d) ^ 2) : ℂ) ∧
    ∀ t ⊆ s, magnitude (overlapCoefficient t c a d) ≤
      if t.card ≤ d then (∏ j ∈ t, ‖a j‖) * (‖c‖ + ∑ j ∈ t, ‖a j‖) ^ (d - t.card) /
        ((d - t.card).factorial : ℝ) else 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (J := ULift.{u} Unit) ∅ (fun _ => 0) 0
  norm_num [rejected, realize, disjointSeries] at hz

def evidence : Registration arena.{u} (type_of% @signed_overlap_expansion.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signed_overlap_expansion.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@signed_overlap_expansion.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.DisjointCharacterRemainder.Expansion.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.DisjointCharacterRemainder.Expansion.evidence
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
    owner := `D5.S3.Fourier.Concentration.DisjointCharacterRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Expansion

namespace Remainder

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => fun z : ℂ => ‖z‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} (s : Finset J) (a : J → ℂ) (d K : ℕ),
    let c := ∑ j ∈ s, a j
    let squareNorm := V.readout () ()
    let admissible := s.powerset.filter (fun t => t.card ≤ d)
    let small := admissible.filter (fun t => t.card ≤ K)
    let large := admissible.filter (fun t => K < t.card)
    let square := fun t => squareNorm (overlapCoefficient t c a d)
    let bound := fun t => ((∏ j ∈ t, ‖a j‖) * (‖c‖ + ∑ j ∈ t, ‖a j‖) ^ (d - t.card) /
        ((d - t.card).factorial : ℝ)) ^ 2
    let remainder := (coeff d (coeff d (disjointSeries s a (fun j => conj (a j))))).re -
      ∑ t ∈ small, (-1 : ℝ) ^ t.card * square t
    remainder = (∑ t ∈ large.filter (fun t => Even t.card), square t) -
      (∑ t ∈ large.filter (fun t => ¬ Even t.card), square t) ∧
    -(∑ t ∈ large.filter (fun t => ¬ Even t.card), bound t) ≤ remainder ∧
    remainder ≤ ∑ t ∈ large.filter (fun t => Even t.card), bound t

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (J := ULift.{u} Unit) ∅ (fun _ => 0) 0 0
  norm_num [rejected, realize, disjointSeries] at hz

def evidence : Registration arena.{u} (type_of% @signed_overlap_remainder.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signed_overlap_remainder.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@signed_overlap_remainder.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.DisjointCharacterRemainder.Remainder.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.DisjointCharacterRemainder.Remainder.evidence
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
    owner := `D5.S3.Fourier.Concentration.DisjointCharacterRemainder
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

end Remainder

end

end Reg.D5.S3.Fourier.Concentration.DisjointCharacterRemainder
