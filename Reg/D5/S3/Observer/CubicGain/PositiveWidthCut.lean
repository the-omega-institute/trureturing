import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.PositiveWidthCut
import Reg.Support.SingleDependentReadout

/-! The native width comparison varies while the complete source proposition is retained. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.PositiveWidthCut
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ β : ℝ,
    (0 < β ∧ β^3-8*β-4=0 ∧
      ∀ x : ℝ, 0 < x → x^3-8*x-4=0 → x=β) ∧
    (∀ C : Coordinates, StrictParent C → 0 < fifthResponse C → R.readout () () C.2.1 β) ∧
    (∀ W : OriginalWorld, OriginalParent W → 0 < originalRead W 5 → W.2.1 < β)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨β,hβ,hnative,_⟩
  exact hnative (1/2,1/8,0)
    (by norm_num [StrictParent,parentEq])
    (by norm_num [fifthResponse,fifthDrift,sourceN,sourceJ])

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have hh : (1:ℝ) < 1 := Eq.mp (congrFun h 1) (by norm_num : (0:ℝ) < 1)
  exact (lt_irrefl 1) hh

def source_registration : Registration arena (type_of% @positive_parent_width_cut) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive_parent_width_cut,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@positive_parent_width_cut) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.PositiveWidthCut.positive_parent_width_cut.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.PositiveWidthCut.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.PositiveWidthCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg","body","arg","fn","arg","body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Reg.D5.S3.Observer.CubicGain.PositiveWidthCut
