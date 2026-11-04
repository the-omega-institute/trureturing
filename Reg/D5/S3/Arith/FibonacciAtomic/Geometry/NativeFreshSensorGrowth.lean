import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair (Call run Value RawMap nativeRun)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition (D material terminals neighbors children)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector (basis)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

@[reducible] def signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Call → Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ t => run t) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ _ => none) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ t : Source, R.readout () () t (calls t) = some (grown t)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (.of true)
  change none = some (grown (.of true)) at hh
  contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), .of true, .of false, ?_⟩
  intro he
  have hh := congrFun he []
  change some (FreeMagma.of true : Source) = some (.of false) at hh
  cases hh

def executesFamilyRegistration : Registration arena (type_of% executes) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨executes, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence }

noncomputable def executesRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@executes) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth.executes "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth.executesFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨executesFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

@[reducible] def nativeSignature : Signature where
  Params := RawMap × ℤ × Value
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Call → Option (Source × RawMap × ℤ × Value)
  Anchor := Empty
  finiteAnchor := inferInstance

def nativeActual : Realization nativeSignature :=
  realize nativeSignature (fun _ s t => nativeRun t s.1 s.2.1 s.2.2) (fun e => nomatch e)
def nativeBad : Realization nativeSignature :=
  realize nativeSignature (fun _ _ _ _ => none) (fun e => nomatch e)
@[reducible] def valuesArena : Arena where
  signature := nativeSignature
  Law R := ∀ (t : Source), D t → ∀ (labels : RawMap) (next : ℤ) (x : Value),
    ∃ labels' next' y,
      R.readout () (labels,next,x) t (calls t) = some (grown t,labels',next',y) ∧
      (∀ p ∈ material t, y p = x p) ∧
      (∀ p ∈ material (grown t), p ∉ material t → y p = 0)
private theorem values_bad : ¬ valuesArena.Law nativeBad := by
  intro h
  have hd : D (.of true) := by intro p; cases p <;> simp [readout]
  obtain ⟨l,n,y,hr,_⟩ := h (.of true) hd (fun _ => []) 0 0
  change none = some _ at hr
  contradiction
theorem native_dependence : ObservationalDependence nativeSignature nativeActual := by
  intro i
  cases i
  refine ⟨((fun _ => []),0,0), .of true, .of false, ?_⟩
  intro he
  have hh := congrFun he []
  have hh' := congrArg (Option.map (fun r => r.1)) hh
  change some (FreeMagma.of true : Source) = some (.of false) at hh'
  cases hh'
def valuesFamilyRegistration : Registration valuesArena (type_of% actual_values) := {
  actual := nativeActual
  bridge := Iff.rfl
  variation := ⟨actual_values,nativeBad,values_bad⟩
  sensitivity := ⟨fun i => ⟨nativeBad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, values_bad⟩,
    fun e => nomatch e⟩
  dependence := native_dependence }

@[reducible] def inventorySignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Address
  Anchor := Empty
  finiteAnchor := inferInstance

def inventoryActual : Realization inventorySignature :=
  realize inventorySignature (fun _ _ t => material (grown t)) (fun e => nomatch e)
def inventoryBad : Realization inventorySignature :=
  realize inventorySignature (fun _ _ _ => []) (fun e => nomatch e)
@[reducible] def inventoryArena : Arena where
  signature := inventorySignature
  Law R := ∀ t : Source,
    (R.readout () () t).length + 1 =
      5 * (_root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.composition t).1 + 7 * (_root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.composition t).2 ∧
    (terminals (grown t)).length =
      2 * (_root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.composition t).1 + 3 * (_root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.composition t).2 ∧
    (sensors t).length = (_root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.leaves t).length ∧
    (∀ p ∈ sensors t, p ∈ terminals (grown t))
private theorem inventory_bad : ¬ inventoryArena.Law inventoryBad := by
  intro h
  have hh := (h (.of true)).1
  norm_num [inventoryBad,realize,_root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.composition] at hh
private theorem inventory_dependence : ObservationalDependence inventorySignature inventoryActual := by
  intro i
  cases i
  refine ⟨(), .of true, .of false, ?_⟩
  intro he
  have hh := congrArg List.length he
  norm_num [inventoryActual,realize,grown,cone,material] at hh
def inventoryFamilyRegistration : Registration inventoryArena (type_of% inventory) := {
  actual := inventoryActual
  bridge := Iff.rfl
  variation := ⟨inventory,inventoryBad,inventory_bad⟩
  sensitivity := ⟨fun i => ⟨inventoryBad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, inventory_bad⟩,
    fun e => nomatch e⟩
  dependence := inventory_dependence }

@[reducible] def updateSignature : Signature where
  Params := Source
  State _ := Value
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Value
  Anchor := Empty
  finiteAnchor := inferInstance

def updateActual : Realization updateSignature :=
  realize updateSignature (fun _ t => update t) (fun e => nomatch e)
def updateBad : Realization updateSignature :=
  realize updateSignature (fun _ _ _ => basis []) (fun e => nomatch e)
@[reducible] def liftArena : Arena where
  signature := updateSignature
  Law R := ∀ (l r : Source) (b : Bool) (x : Value), x [] = 0 →
    R.readout () (.mul l r) (lift b x) = lift b (R.readout () (if b then r else l) x)
private theorem lift_bad : ¬ liftArena.Law updateBad := by
  intro h
  have hh := congrFun (h (.of true) (.of true) false 0 rfl) []
  norm_num [updateBad,realize,basis,lift] at hh
private theorem update_dependence : ObservationalDependence updateSignature updateActual := by
  intro i
  cases i
  refine ⟨.of false, 0, basis [], ?_⟩
  intro he
  have hh := congrFun he [false]
  norm_num [updateActual,realize,update,material,neighbors,children,readout,basis,Pi.zero_apply] at hh
  change (0 : ℚ) = 1 at hh
  norm_num at hh
def liftFamilyRegistration : Registration liftArena (type_of% update_lift) := {
  actual := updateActual
  bridge := Iff.rfl
  variation := ⟨update_lift,updateBad,lift_bad⟩
  sensitivity := ⟨fun i => ⟨updateBad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, lift_bad⟩,
    fun e => nomatch e⟩
  dependence := update_dependence }

noncomputable def valuesRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_values) (type_of% (realize nativeSignature nativeActual.readout nativeActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth.actual_values "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth.valuesFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨valuesArena⟩
  objectArena := .source ⟨valuesArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source valuesArena ⟨valuesFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize nativeSignature nativeActual.readout nativeActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def inventoryRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inventory) (type_of% (realize inventorySignature inventoryActual.readout inventoryActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth.inventory "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth.inventoryFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨inventoryArena⟩
  objectArena := .source ⟨inventoryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inventoryArena ⟨inventoryFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize inventorySignature inventoryActual.readout inventoryActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def liftRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@update_lift) (type_of% (realize updateSignature updateActual.readout updateActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth.update_lift "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth.liftFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨liftArena⟩
  objectArena := .source ⟨liftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source liftArena ⟨liftFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize updateSignature updateActual.readout updateActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
