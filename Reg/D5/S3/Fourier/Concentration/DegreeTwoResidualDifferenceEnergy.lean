import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy

/-! Dependence of the directed difference frequency on its endpoints. -/

namespace Reg.D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (nearCollisionMass)
open _root_.D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x.1 - x.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J]
      (g w : J → ℝ) {η : ℝ}, 0 ≤ η →
    let rate := V.readout () ()
    degreeTwoResidualMass g w η =
      nearCollisionMass ((univ : Finset (J × J)).filter (fun e => e.1 ≠ e.2))
        (fun e => rate (g e.1, g e.2)) (fun e => w e.1 * w e.2) η -
      2 * (∑ i, w i ^ 2 * nearCollisionMass (univ.erase i) g w η) +
        ∑ i, ∑ j ∈ univ.erase i, w i ^ 2 * w j ^ 2

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  classical
  let g (j : ULift.{u} Bool) : ℝ := if j.down then 1 else 0
  let w : ULift.{u} Bool → ℝ := fun _ => 1
  have h := law g w (η := 0) (le_refl 0)
  have hactual := degree_two_residual g w (η := 0) (le_refl 0)
  change
    degreeTwoResidualMass g w 0 =
      nearCollisionMass ((univ : Finset (ULift.{u} Bool × ULift.{u} Bool)).filter
        (fun e => e.1 ≠ e.2)) (fun _ => 0) (fun e => w e.1 * w e.2) 0 -
      2 * (∑ i, w i ^ 2 * nearCollisionMass (univ.erase i) g w 0) +
        ∑ i, ∑ j ∈ univ.erase i, w i ^ 2 * w j ^ 2 at h
  dsimp only at hactual
  rw [h] at hactual
  have hu : (univ : Finset (ULift.{u} Bool)) = {ULift.up false, ULift.up true} := by
    ext ⟨b⟩
    cases b <;> simp
  have henergy :
      (univ : Finset (ULift.{u} Bool × ULift.{u} Bool)).filter (fun e => e.1 ≠ e.2) =
        {(ULift.up false, ULift.up true), (ULift.up true, ULift.up false)} := by
    ext ⟨⟨a⟩, ⟨b⟩⟩
    cases a <;> cases b <;> simp
  rw [henergy] at hactual
  apply add_right_cancel at hactual
  apply sub_left_inj.mp at hactual
  norm_num [nearCollisionMass, hu, g, w, Finset.sum_insert, Finset.filter_insert, Finset.filter_singleton] at hactual

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  change (0 : ℝ) - 0 ≠ 1 - 0
  norm_num

def evidence : Registration arena.{u} (type_of% @degree_two_residual.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@degree_two_residual.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@degree_two_residual.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.1 - x.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy
