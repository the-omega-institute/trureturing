import D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
open D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
open D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
abbrev signature : Signature where
  Params := {P : CutSet // CutPrefixFree P} × Source
  State p := LegalValues (canonicalRow p.1.val p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => canonicalRow p.1.val (evaluateRow (extend _ v.val) (canonicalRow p.1.val p.2)))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : CutSet) (hP : CutPrefixFree P) (u : Source)
    (v : LegalValues (canonicalRow P u)), R.readout () (⟨P,hP⟩,u) v = canonicalRow P u

theorem bridge : (type_of% (@legal_values_row)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := legal_values_row

/-- On every admitted prefix-free parameter fiber the faithful old-row output
is constant, so this readout cannot supply observational dependence there. -/
theorem invariant_on_legal_fiber (P : CutSet) (hP : CutPrefixFree P) (u : Source)
    (v w : LegalValues (canonicalRow P u)) : actual.readout () (⟨P,hP⟩,u) v = actual.readout () (⟨P,hP⟩,u) w :=
  (legal_values_row P hP u v).trans (legal_values_row P hP u w).symm

/-- This faithful invariant-row readout fails the enrolled template's
observational-dependence obligation on its complete legal-state domain. -/
theorem dependence_impossible : ¬ ObservationalDependence signature actual := by
  intro dep
  obtain ⟨p,v,w,ne⟩ := dep ()
  exact ne (invariant_on_legal_fiber p.1.val p.1.property p.2 v w)

#print axioms bridge
#print axioms actual_law
#print axioms invariant_on_legal_fiber
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.Labels
abbrev signature : Signature where
  Params := CutSet
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p u => labels (canonicalRow p u)) (fun e => nomatch e)

def bad : Realization signature := realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : CutSet) (u : Source), R.readout () P u =
    (orderedHoles P u).toFinset.image (classOrdinal P u)

theorem bridge : (type_of% (@labels_canonical)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := labels_canonical

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have eq := law {[]} (.of true)
  change (∅ : Finset Nat) =
    (orderedHoles {[]} (.of true)).toFinset.image (classOrdinal {[]} (.of true)) at eq
  have order : orderedHoles {[]} (.of true) = [[]] := by simp [orderedHoles, reachedHoles]
  rw [order] at eq
  simp at eq

def proof : Registration arena (type_of% (@labels_canonical)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    have role : i = () := Subsingleton.elim _ _
    subst i
    refine ⟨{[true]},.of true,.mul (.of true) (.of true),?_⟩
    intro eq
    have absent : actual.readout () {[true]} (.of true) = ∅ := by
      simp [actual, realize, canonicalRow, literalRow, labels]
    have present : actual.readout () {[true]} (.mul (.of true) (.of true)) =
        {classOrdinal {[true]} (.mul (.of true) (.of true)) [true]} := by
      simp [actual, realize, canonicalRow, literalRow, labels]
    rw [absent, present] at eq
    simp at eq

noncomputable def labels_canonical_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.labels_canonical)
    (Realization signature) ((P : CutSet) → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.labels_canonical
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.Labels.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p u => labels (canonicalRow p u)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
#print axioms labels_canonical_registration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.Labels

noncomputable section

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.FullRootSuppliers
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev reconstructionSignature : Signature where
  Params := LiteralRow
  State p := Nat → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def reconstructionActual : Realization reconstructionSignature := realize reconstructionSignature
  (fun _ C f => evaluateRow f C) (fun e => nomatch e)
def reconstructionBad : Realization reconstructionSignature := realize reconstructionSignature
  (fun _ _ _ => .of true) (fun e => nomatch e)
abbrev reconstructionArena : Arena where
  signature := reconstructionSignature
  Law R := ∀ (P : CutSet) (hP : CutPrefixFree P) (C : LiteralRow) (u : RowFiber P C), R.readout () C (extend C (recover P hP C u).val) = u.val

private theorem reconstructionBadLaw : ¬ reconstructionArena.Law reconstructionBad := by
  intro h
  have hp : CutPrefixFree ∅ := by intro a ha b hb _; simp at ha
  let C : LiteralRow := .of (.inl false)
  have hu : canonicalRow ∅ (.of false) = C := rfl
  have eq := h ∅ hp C ⟨.of false,hu⟩
  change FreeMagma.of true = FreeMagma.of false at eq
  cases eq

private theorem reconstructionDependence : ObservationalDependence reconstructionSignature reconstructionActual := by
  intro i
  refine ⟨.of (.inr 0),(fun _ => .of true),(fun _ => .of false),?_⟩
  intro eq
  change FreeMagma.of true = FreeMagma.of false at eq
  cases eq

def reconstructionFamily : Registration reconstructionArena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.recover_fill)) where
  actual := reconstructionActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.recover_fill,reconstructionBad,reconstructionBadLaw⟩
  sensitivity := ⟨fun i => ⟨reconstructionBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,reconstructionBadLaw⟩,fun i => nomatch i⟩
  dependence := reconstructionDependence

def reconstructionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.recover_fill)
    (type_of% (realize reconstructionSignature reconstructionActual.readout reconstructionActual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.recover_fill.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.FullRootSuppliers.reconstructionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨reconstructionArena⟩
  objectArena := .source ⟨reconstructionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reconstructionArena ⟨reconstructionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize reconstructionSignature reconstructionActual.readout reconstructionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms reconstructionRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers.FullRootSuppliers
