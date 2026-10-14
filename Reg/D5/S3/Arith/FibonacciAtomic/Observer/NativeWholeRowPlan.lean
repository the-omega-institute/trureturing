import D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowPlan

/- The relocated supporting theorems retain their incomplete four-slot audits.
   No validated registration is claimed. The missing enrolled-template and
   realization evidence is tracked with the whole-row audits at
   https://github.com/the-omega-institute/trureturing/issues/15604. -/

noncomputable section

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowPlan.FullRootSuppliers
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev representativeSignature : Signature where
  Params := Σ C : LiteralRow, Classes C
  State p := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

def representativeActual : Realization representativeSignature := realize representativeSignature
  (fun _ p t => subtree (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.representative p.1 p.2) t) (fun e => nomatch e)
def representativeBad : Realization representativeSignature := realize representativeSignature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev representativeArena : Arena where
  signature := representativeSignature
  Law R := ∀ (C : LiteralRow) (v : Classes C → Source) (d : Classes C), R.readout () ⟨C,d⟩ (evaluateRow (extend C v) C) = some (v d)

private theorem representativeBadLaw : ¬ representativeArena.Law representativeBad := by
  intro h
  let d : Classes (.of (.inr 0)) := ⟨0,by simp [labels]⟩
  have eq := h (.of (.inr 0)) (fun _ => .of true) d
  change none = some (FreeMagma.of true) at eq
  cases eq

private theorem representativeDependence : ObservationalDependence representativeSignature representativeActual := by
  intro i
  let d : Classes (.of (.inr 0)) := ⟨0,by simp [labels]⟩
  refine ⟨⟨.of (.inr 0),d⟩,.of true,.of false,?_⟩
  intro eq
  have address : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.representative (.of (.inr 0)) d = [] := by
    simp [_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.representative,d,holeAddresses,holeLabel,rowAt]
  simp only [representativeActual,realize,address,subtree,Option.some.injEq] at eq
  cases eq

def representativeFamily : Registration representativeArena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.representative_subtree)) where
  actual := representativeActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.representative_subtree,representativeBad,representativeBadLaw⟩
  sensitivity := ⟨fun i => ⟨representativeBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,representativeBadLaw⟩,fun i => nomatch i⟩
  dependence := representativeDependence

def representativeRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.representative_subtree)
    (type_of% (realize representativeSignature representativeActual.readout representativeActual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowPlan.representative_subtree.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowPlan.FullRootSuppliers.representativeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨representativeArena⟩
  objectArena := .source ⟨representativeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source representativeArena ⟨representativeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize representativeSignature representativeActual.readout representativeActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowPlan
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms representativeRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowPlan.FullRootSuppliers
