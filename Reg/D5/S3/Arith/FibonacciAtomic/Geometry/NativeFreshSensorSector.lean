import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair (Value)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth (grown update)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
@[reducible] def signature : Signature where
  Params := Source
  State _ := Value
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Value
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t => adjacency (grown t)) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

@[reducible] def actionsArena : Arena where
  signature := signature
  Law R := ∀ (t : Source) (p : Address), subtree p t = some (.mul (.of false) (.of false)) →
    R.readout () t (vector p []) = vector p [false] + vector p [true] ∧
    R.readout () t (vector p [false]) =
      vector p [] + vector p [false, false] + vector p [false, true] ∧
    R.readout () t (vector p [false, false]) =
      vector p [false] + vector p [false, false, false] ∧
    R.readout () t (vector p [false, false, false]) = vector p [false, false] ∧
    R.readout () t (vector p [true]) = vector p [] ∧
    R.readout () t (vector p [false, true]) = vector p [false]

@[reducible] def powersArena : Arena where
  signature := signature
  Law R := ∀ (t : Source) (p : Address), subtree p t = some (.mul (.of false) (.of false)) →
    R.readout () t (half p) =
      (1 / 2 : ℚ) • (vector p [true] - vector p [false, false, false]) ∧
    R.readout () t (R.readout () t (half p)) = half p ∧
    (R.readout () t)^[2] (vector p []) =
      (2 : ℚ) • vector p [] + vector p [false, false] + vector p [false, true] ∧
    (R.readout () t)^[2] (vector p [false, true]) =
      vector p [] + vector p [false, false] + vector p [false, true] ∧
    (R.readout () t)^[4] (vector p []) =
      (6 : ℚ) • vector p [] + (5 : ℚ) • vector p [false, false] +
        (4 : ℚ) • vector p [false, true]

private theorem actions_bad : ¬ actionsArena.Law bad := by
  intro h
  have hh := congrFun (h (.mul (.of false) (.of false)) [] rfl).1 [false,false]
  norm_num [bad,realize,vector,basis] at hh
private theorem powers_bad : ¬ powersArena.Law bad := by
  intro h
  have hh := congrFun (h (.mul (.of false) (.of false)) [] rfl).1 [false,true]
  norm_num [bad,realize,vector,basis] at hh
theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨.mul (.of false) (.of false), 0, vector [] [], ?_⟩
  intro he
  have hh := congrFun he [false,false]
  have ha := (attained_actions (.mul (.of false) (.of false)) [] rfl).1
  simp only [actual,realize] at hh
  change update (grown (.mul (.of false) (.of false))) 0 [false,false] =
    update (grown (.mul (.of false) (.of false))) (vector [] []) [false,false] at hh
  have hz : update (grown (.mul (.of false) (.of false))) 0 = 0 :=
    map_zero (adjacency (grown (.mul (.of false) (.of false))))
  rw [hz,ha] at hh
  norm_num [vector,basis,Pi.zero_apply] at hh

def actionsFamilyRegistration : Registration actionsArena (type_of% attained_actions) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨attained_actions, bad, actions_bad⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, actions_bad⟩,
    fun e => nomatch e⟩
  dependence := dependence }

noncomputable def actionsRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@attained_actions) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector.attained_actions "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector.actionsFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨actionsArena⟩
  objectArena := .source ⟨actionsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source actionsArena ⟨actionsFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def powersFamilyRegistration : Registration powersArena (type_of% attained_powers) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨attained_powers, bad, powers_bad⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, powers_bad⟩,
    fun e => nomatch e⟩
  dependence := dependence }

noncomputable def powersRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@attained_powers) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector.attained_powers "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector.powersFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨powersArena⟩
  objectArena := .source ⟨powersArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source powersArena ⟨powersFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
