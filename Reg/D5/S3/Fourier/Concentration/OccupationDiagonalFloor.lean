import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.OccupationDiagonalFloor

/-! Dependence of the occupation floor on box widths and the Fejer kernel. -/

namespace Reg.D5.S3.Fourier.Concentration.OccupationDiagonalFloor

open Finset MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.OccupationDiagonalFloor
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open _root_.D5.S3.Analytic.Fourier.AngularFejerKernel
open _root_.Reg.Support

noncomputable section
universe u

namespace Box

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => 1+2*x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual,realize]

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J] (w : J → ℝ),
    (∀ j, 0≤w j) → (∑ j,w j=1) → ∀ (j0 : J) (p : ℕ)
    (r : {j : J // j ≠ j0} → ℝ), (∀ j, 0 < r j) →
    let width := R.readout () ()
    let v := ∑ j : {j : J // j ≠ j0}, (p:ℝ)*(w j.1-(w j.1)^2)/(r j)^2
    (max 0 (1-v))^2 ≤ (∏ j,width (r j))*diagonal w p

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  classical
  let j0 : ULift.{u} (Fin 2) := ⟨0⟩
  let w : ULift.{u} (Fin 2) → ℝ := fun _ => 1/2
  have hW : ∑ j,w j = 1 := by
    rw [← (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)).sum_comp w]
    norm_num [w,Fin.sum_univ_two]
  let : Nonempty {j : ULift.{u} (Fin 2) // j ≠ j0} := ⟨⟨⟨1⟩,by decide⟩⟩
  have h := law w (fun _ => by dsimp [w]; positivity) hW j0 0 (fun _ => 1) (fun _ => zero_lt_one)
  have hh : (1:ℝ) ≤ 0 := by simpa [rejected,realize] using h
  norm_num at hh

def evidence : Registration arena.{u} (type_of% @occupation_diagonal_lower.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@occupation_diagonal_lower.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@occupation_diagonal_lower.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.OccupationDiagonalFloor.Box.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.OccupationDiagonalFloor.Box.evidence
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
    owner := `D5.S3.Fourier.Concentration.OccupationDiagonalFloor
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Box

namespace Fejer

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => K z.1 z.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1,0), (2,0), ?_⟩
  change K 1 0 ≠ K 2 0
  simp [K]
  have hp := Real.pi_pos
  field_simp
  norm_num

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J] (g w : J → ℝ),
    (∀ j, 0≤w j) → (∑ j,w j=1) → ∀ (j0 : J) (p : ℕ)
    (r : {j : J // j ≠ j0} → ℝ), (∀ j, 0 < r j) → ∀ η : ℝ, 0<η →
    let kernel := R.readout () ()
    let v := ∑ j : {j : J // j ≠ j0}, (p:ℝ)*(w j.1-(w j.1)^2)/(r j)^2
    (max 0 (1-v))^2 ≤ (∏ j : {j : J // j ≠ j0},(1+2*r j))*
      (∫ t : ℝ,kernel (η,t)*‖complexScore g w t‖^(2*p))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h := law (J := ULift.{u} Unit) (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one) (by simp) ⟨()⟩ 0 (fun _ => 1) (fun _ => zero_lt_one) 1 zero_lt_one
  norm_num [rejected,realize] at h

def evidence : Registration arena.{u} (type_of% @fejer_occupation_floor.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fejer_occupation_floor.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@fejer_occupation_floor.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.OccupationDiagonalFloor.Fejer.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.OccupationDiagonalFloor.Fejer.evidence
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
    owner := `D5.S3.Fourier.Concentration.OccupationDiagonalFloor
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Fejer

end
end Reg.D5.S3.Fourier.Concentration.OccupationDiagonalFloor
