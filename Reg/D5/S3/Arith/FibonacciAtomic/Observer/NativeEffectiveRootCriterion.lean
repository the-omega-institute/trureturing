import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveRootCriterion
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveRootCriterion
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveRootCriterion
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine (Run answers)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization (Dialogue)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private def zero : LiteralRow := .of (.inl false)
private theorem empty_prefix : CutPrefixFree ∅ := by
  intro a ha
  change a ∈ (∅ : CutSet) at ha
  simp at ha
private theorem zero_actual : Nonempty (OriginFiber ∅ zero) := ⟨⟨.of true,rfl⟩⟩



namespace Reader
abbrev signature : Signature where
  Params := Σ _ : LiteralRow, Nat
  State p := RootPackage p.1 p.2 × Fin p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Dialogue LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p state => nativeEntry p.1 state.1 state.2) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .stop (.of (.inl false))) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : CutSet) (hP : CutPrefixFree P) (C : LiteralRow)
    (actual : Nonempty (OriginFiber P C)) (r q : Nat) (hr : 1 ≤ r)
    (pkg : RootPackage C r) (hp : decideNative C r q = some pkg),
    (Set.range (acquiredEncoder P hP C actual pkg)).Finite ∧
    (Set.range (acquiredEncoder P hP C actual pkg)).ncard ≤ r ∧
    ∀ (v : ImageValues C) (u : OriginFiber P C),
      substitution u.val = evaluateRow (extend C v.val.val) C →
      ∃ tr, Run controller (R.readout () ⟨C,r⟩ (pkg,acquiredEncoder P hP C actual pkg v))
          0 (substitution u.val) tr (canonicalRow P u.val) ∧
        Stationary tr ∧ (answers tr).length ≤ q

private def values : ImageValues zero :=
  ⟨⟨fun _ => .of false,by
    intro a b _
    have hn := a.property
    simp [zero,labels] at hn⟩,⟨.of true,rfl⟩⟩

private theorem badLaw : ¬ arena.Law bad := by
  intro h
  have ht : (decideNative zero 1 0).isSome = true := by decide +kernel
  cases hp : decideNative zero 1 0 with
  | none => simp [hp] at ht
  | some pkg =>
      obtain ⟨tr,run,_,_⟩ := (h ∅ empty_prefix zero zero_actual 1 0 (by decide) pkg hp).2.2
        values ⟨.of true,rfl⟩ rfl
      cases run <;> simp_all [controller,bad,realize,zero,canonicalRow,literalRow]
      rename_i he
      cases he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let a : RootPackage zero 1 := {color := fun _ => 0,tree := fun _ => .stop (.of (.inl false))}
  let b : RootPackage zero 1 := {color := fun _ => 0,tree := fun _ => .stop (.of (.inl true))}
  refine ⟨⟨zero,1⟩,(a,0),(b,0),?_⟩
  intro he
  change Dialogue.stop (FreeMagma.of (Sum.inl false) : LiteralRow) =
    Dialogue.stop (FreeMagma.of (Sum.inl true) : LiteralRow) at he
  cases he

def family : Registration arena (type_of% (@returned_native_reader)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨returned_native_reader,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@returned_native_reader)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveRootCriterion.returned_native_reader.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveRootCriterion.Reader.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveRootCriterion
    definition := none
    coordinates := #[0,2,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg","fn","arg","body","body","body","body","fn","arg","fn","arg","arg"],
      stateBinder := 7,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration
end Reader

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveRootCriterion
