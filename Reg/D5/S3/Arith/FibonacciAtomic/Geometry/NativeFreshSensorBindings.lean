import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings
import Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
import Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address readout leaves)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition (D material terminals)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair (Value RawMap nativeRun zeroExtend)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth (calls grown sensors)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector (vector half adjacency basis)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings
open NativeFreshSensorGrowth (nativeSignature nativeActual native_dependence)
noncomputable section
def bad : Realization nativeSignature :=
  realize nativeSignature (fun _ s t _ => some (t,s.1,s.2.1,s.2.2)) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := nativeSignature
  Law R := ∀ {t u : Source} {labels labels' : RawMap} {next next' : ℤ} {x y : Value},
    R.readout () (labels,next,x) t (calls t) = some (u,labels',next',y) →
    next' = next + (fresh t).length ∧
    (∀ i, i < next → labels i ∈ terminals t → labels' i = inherited t (labels i)) ∧
    (∀ j (hj : j < (fresh t).length), labels' (next + j) = (fresh t)[j])
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := (h (t := .of true) (u := .of true) (labels := fun _ => [])
    (labels' := fun _ => []) (next := 0) (next' := 0) (x := 0) (y := 0) rfl).1
  norm_num [fresh] at hh
def familyRegistration : Registration arena (type_of% @raw_bindings) := {
  actual := nativeActual
  bridge := Iff.rfl
  variation := ⟨@raw_bindings,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := native_dependence }

noncomputable def rawRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@raw_bindings) (type_of% (realize nativeSignature nativeActual.readout nativeActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings.raw_bindings "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize nativeSignature nativeActual.readout nativeActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings
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
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings
