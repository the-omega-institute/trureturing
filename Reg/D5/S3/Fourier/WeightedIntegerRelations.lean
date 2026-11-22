import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.WeightedIntegerRelations

/-! An audit of the character chord using the norm of the product difference. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace Reg.D5.S3.Fourier.WeightedIntegerRelations

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.WeightedIntegerRelations
open _root_.Reg.Support

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

theorem norm_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (0 : ℂ), 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  simp

def chordArena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} (columns : Finset J) (z q : J → Circle) (k : J → ℤ),
    R.readout () () (((∏ j ∈ columns, z j ^ k j : Circle) : ℂ) -
      ((∏ j ∈ columns, q j ^ k j : Circle) : ℂ)) ≤
      ∑ j ∈ columns, |(k j : ℝ)| * ‖(z j : ℂ) - (q j : ℂ)‖

private theorem chord_rejected : ¬ chordArena.{u}.Law rejected := by
  intro h
  have hbad := h (J := ULift.{u} Unit) ∅ (fun _ => 1) (fun _ => 1) (fun _ => 0)
  change (2 : ℝ) ≤ ∑ j ∈ (∅ : Finset (ULift.{u} Unit)),
    |((0 : ℤ) : ℝ)| * ‖((1 : Circle) : ℂ) - ((1 : Circle) : ℂ)‖ at hbad
  simp only [Finset.sum_empty] at hbad
  norm_num at hbad

def chordFamily : Registration chordArena.{u} (type_of% @chord_prod_zpow.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨chord_prod_zpow, rejected, chord_rejected⟩
  sensitivity := SingleDependentReadout.sensitivity chordArena.Law actual rejected chord_rejected
  dependence := norm_dependence

def chordAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@chord_prod_zpow.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Fourier.WeightedIntegerRelations.chord_prod_zpow.__information_unit
  realizationName := `Reg.D5.S3.Fourier.WeightedIntegerRelations.chordFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chordArena⟩
  objectArena := .source ⟨chordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chordArena ⟨chordFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedIntegerRelations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms chordAudit

end Reg.D5.S3.Fourier.WeightedIntegerRelations
