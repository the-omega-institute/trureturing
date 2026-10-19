import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.UniformValues
import Reg.Support.SingleDependentReadout

noncomputable section
open Matrix
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.UniformValues
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Subentropy.UniformValues
universe u
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.log x + 1) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, Real.exp 1, ?_⟩
  norm_num [actual, realize]

namespace Two
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [di : DecidableEq ι],
    Fintype.card ι = 2 →
    matrixSubentropy (diagonal (fun _ : ι => ((1 / 2 : ℝ) : ℂ))) =
      R.readout () () 2 - 1 / 2
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} (Fin 2)) inferInstance inferInstance (by simp)
  have hv := subentropy_uniformTwo (ι := ULift.{u} (Fin 2)) (by simp)
  change matrixSubentropy _ = Real.log 2 + 1 - 1 / 2 at hb
  linarith
def family : Registration arena.{u} (type_of% @subentropy_uniformTwo.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@subentropy_uniformTwo, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@subentropy_uniformTwo.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.UniformValues.subentropy_uniformTwo.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.UniformValues.Two.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.UniformValues
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Two

namespace Four
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [di : DecidableEq ι],
    Fintype.card ι = 4 →
    matrixSubentropy (diagonal (fun _ : ι => ((1 / 4 : ℝ) : ℂ))) =
      R.readout () () 4 - 13 / 12
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} (Fin 4)) inferInstance inferInstance (by simp)
  have hv := subentropy_uniformFour (ι := ULift.{u} (Fin 4)) (by simp)
  change matrixSubentropy _ = Real.log 4 + 1 - 13 / 12 at hb
  linarith
def family : Registration arena.{u} (type_of% @subentropy_uniformFour.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@subentropy_uniformFour, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@subentropy_uniformFour.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.UniformValues.subentropy_uniformFour.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.UniformValues.Four.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.UniformValues
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Four

end Reg.D5.S3.Quantum.Subentropy.UniformValues
