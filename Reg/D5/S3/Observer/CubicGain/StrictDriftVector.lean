import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.StrictDriftVector
import Reg.Support.SingleDependentReadout

/-! Faithful dependent-readout registration of the source statements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.StrictDriftVector
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Numerator
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ r b => n4 r b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (r b : ℝ), b≠0 → sourceJ r b≠0 → sourceN r b≠0 →
    1+b≠0 → 1+2*b≠0 → R.readout () r b =
      (1+b)*(1+2*b)*(b^2+r-r^2)*(b^2+r-r^2+b*r)*parentLambda r b
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1/2) (1/2) (by norm_num) (by norm_num [sourceJ])
    (by norm_num [sourceN,sourceJ]) (by norm_num) (by norm_num)
  norm_num [rejected,realize,parentLambda,sourceJ,sourceN] at hh
def family : Registration arena (type_of% @n4_parentLambda) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨n4_parentLambda,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨(1/2 : ℝ),(1/2 : ℝ),(1 : ℝ),?_⟩
    change n4 (1/2) (1/2) ≠ n4 (1/2) 1
    norm_num [n4]
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@n4_parentLambda) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.StrictDriftVector.n4_parentLambda.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.StrictDriftVector.Numerator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r b => n4 r b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.StrictDriftVector
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Numerator

namespace Large
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ r b => parentLambda r b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (r b : ℝ), 0≤r → r≤1 → 0<b → 4≤b → 0<R.readout () r b
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1/2) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected,realize] at hh
def family : Registration arena (type_of% @parentLambda_pos_of_four_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨parentLambda_pos_of_four_le,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨(1/2 : ℝ),(4 : ℝ),(5 : ℝ),?_⟩
    change parentLambda (1/2) 4 ≠ parentLambda (1/2) 5
    norm_num [parentLambda,sourceJ,sourceN]
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@parentLambda_pos_of_four_le) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.StrictDriftVector.parentLambda_pos_of_four_le.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.StrictDriftVector.Large.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r b => parentLambda r b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.StrictDriftVector
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Large
end Reg.D5.S3.Observer.CubicGain.StrictDriftVector
