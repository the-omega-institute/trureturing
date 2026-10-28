import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorAcquisition
import Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
import Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorAcquisition
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address readout leaves)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition (D material terminals)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair (Value RawMap nativeRun zeroExtend)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth (calls grown sensors)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector (vector half adjacency basis)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorAcquisition
open NativeFreshSensorGrowth (nativeSignature nativeActual nativeBad native_dependence)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily (Cherries H)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings (fresh inherited)
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (composition)
noncomputable section
@[reducible] def arena : Arena where
  signature := nativeSignature
  Law R := ∀ (t : Source), D t → ∀ {k : ℕ} (ch : Cherries t k)
    (labels : RawMap) (next : ℤ) (theta : Fin k → ℚ),
    ∃ labels' next' y,
      R.readout () (labels,next,oldField ch theta) t (calls t) =
        some (grown t, labels', next', y) ∧
      (∀ p ∈ material (grown t), y p = zeroExtend t (oldField ch theta) p) ∧
      next' = next + (fresh t).length ∧
      (∀ i, i < next → labels i ∈ terminals t → labels' i = inherited t (labels i)) ∧
      (∀ j (hj : j < (fresh t).length), labels' (next + j) = (fresh t)[j]) ∧
      (∀ p ∈ sensors t, ∃ i, next ≤ i ∧ labels' i = p) ∧
      (material (grown t)).length + 1 = 5 * (composition t).1 + 7 * (composition t).2 ∧
      (terminals (grown t)).length = 2 * (composition t).1 + 3 * (composition t).2 ∧
      (sensors t).length = (leaves t).length ∧
      (∀ p ∈ sensors t, p ∈ terminals (grown t)) ∧
      (∀ i, update (grown t) (vector (ch.root i) []) =
          vector (ch.root i) [false] + vector (ch.root i) [true] ∧
        update (grown t) (vector (ch.root i) [false]) =
          vector (ch.root i) [] + vector (ch.root i) [false,false] + vector (ch.root i) [false,true] ∧
        update (grown t) (vector (ch.root i) [false,false]) =
          vector (ch.root i) [false] + vector (ch.root i) [false,false,false] ∧
        update (grown t) (vector (ch.root i) [false,false,false]) = vector (ch.root i) [false,false] ∧
        update (grown t) (vector (ch.root i) [true]) = vector (ch.root i) [] ∧
        update (grown t) (vector (ch.root i) [false,true]) = vector (ch.root i) [false]) ∧
      (∀ i, adjacency (grown t) (half (ch.root i)) =
          (1 / 2 : ℚ) • (vector (ch.root i) [true] - vector (ch.root i) [false,false,false]) ∧
        adjacency (grown t) (adjacency (grown t) (half (ch.root i))) = half (ch.root i) ∧
        (adjacency (grown t))^[2] (vector (ch.root i) []) =
          (2 : ℚ) • vector (ch.root i) [] + vector (ch.root i) [false,false] + vector (ch.root i) [false,true] ∧
        (adjacency (grown t))^[2] (vector (ch.root i) [false,true]) =
          vector (ch.root i) [] + vector (ch.root i) [false,false] + vector (ch.root i) [false,true] ∧
        (adjacency (grown t))^[4] (vector (ch.root i) []) =
          (6 : ℚ) • vector (ch.root i) [] + (5 : ℚ) • vector (ch.root i) [false,false] +
            (4 : ℚ) • vector (ch.root i) [false,true]) ∧
      (∀ i, observation t (half (ch.root i)) = 0 ∧
        observation t (adjacency (grown t) (half (ch.root i))) = 0) ∧
      Function.Injective (H ch) ∧
      (∀ eta, adjacency (grown t) (adjacency (grown t) (H ch eta)) = H ch eta) ∧
      (∀ eta (j : ℕ), observation t ((adjacency (grown t))^[j] (H ch eta)) = 0) ∧
      (∀ eta p, p ∈ terminals (grown t) → H ch eta p = 0)
private def oneCherry : Cherries (.mul (.of false) (.of false)) 1 where
  root _ := []
  native _ := rfl
  disjoint i j hij := False.elim (hij (Subsingleton.elim i j))
private theorem bad_law : ¬ arena.Law nativeBad := by
  intro h
  have hd : D (.mul (.of false) (.of false)) := by
    intro p
    cases p with
    | nil => simp [readout]
    | cons b p => cases b <;> cases p <;> simp [readout]
  obtain ⟨r,m,y,hr,_⟩ := h _ hd oneCherry (fun _ => []) 0 (fun _ => 0)
  change none = some _ at hr
  contradiction
def familyRegistration : Registration arena (type_of% complete_native_sector) := {
  actual := nativeActual
  bridge := Iff.rfl
  variation := ⟨complete_native_sector,nativeBad,bad_law⟩
  sensitivity := ⟨fun i => ⟨nativeBad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := native_dependence }

noncomputable def completeRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_native_sector) (type_of% (realize nativeSignature nativeActual.readout nativeActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorAcquisition.complete_native_sector "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorAcquisition.familyRegistration
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
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorAcquisition
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
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorAcquisition
