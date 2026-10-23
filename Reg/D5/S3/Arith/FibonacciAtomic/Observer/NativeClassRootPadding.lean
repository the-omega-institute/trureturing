import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev querySignature : Signature where
  Params := Σ _ : CutSet, Σ _ : Source, Address
  State p := Classes (canonicalRow p.1 p.2.1) → Option Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def queryActual : Realization querySignature := realize querySignature
  (fun _ p θ => queryReply (typeExtend (canonicalRow p.1 p.2.1) θ) p.2.2 (canonicalRow p.1 p.2.1))
  (fun e => nomatch e)
def queryBad : Realization querySignature := realize querySignature
  (fun _ _ _ => .absent) (fun e => nomatch e)
abbrev queryArena : Arena where
  signature := querySignature
  Law R := ∀ (P : CutSet) (_ : CutPrefixFree P) (t₀ : Source) (L : Nat)
    (θ : Classes (canonicalRow P t₀) → Option Bool)
    (_ : Admissible (canonicalRow P t₀) θ),
    ∃ v : ImageValues (canonicalRow P t₀), ∃ u : OriginFiber P (canonicalRow P t₀),
      substitution u.val = evaluateRow (extend (canonicalRow P t₀) v.val.val) (canonicalRow P t₀) ∧
      types (canonicalRow P t₀) v.val.val = θ ∧
      DeepValues (canonicalRow P t₀) L v.val.val ∧
      ∀ a : Address, a.length ≤ L →
        readout a (substitution u.val) = R.readout () ⟨P,t₀,a⟩ θ

theorem queryBadLaw : ¬ queryArena.Law queryBad := by
  intro h
  have hp : CutPrefixFree ∅ := by intro a ha; simp at ha
  have hc : canonicalRow ∅ (.of false) = .of (.inl false) := by
    simp [canonicalRow,literalRow]
  have ha : Admissible (canonicalRow ∅ (.of false)) (fun _ => none) := by
    rw [hc]
    simp [Admissible,im]
  obtain ⟨v,u,hu,_,_,hq⟩ := h ∅ hp (.of false) 0 (fun _ => none) ha
  have hh := hq [] (by simp)
  change readout [] (substitution u.val) = Reply.absent at hh
  rw [hu] at hh
  simp [hc,evaluateRow,readout] at hh

theorem queryDependence : ObservationalDependence querySignature queryActual := by
  intro i
  refine ⟨⟨{[]},.of false,[]⟩,(fun _ => some false),(fun _ => none),?_⟩
  intro h
  have hc : canonicalRow {[]} (.of false) = .of (.inr 0) := by
    simp [canonicalRow,literalRow,classOrdinal,orderedHoles,reachedHoles,firstEqIndex,
      _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.subtree]
  change queryReply (typeExtend _ (fun _ => some false)) [] _ =
    queryReply (typeExtend _ (fun _ => none)) [] _ at h
  simp [hc,queryReply,typeExtend,labels,rootReply] at h

def queryFamily : Registration queryArena (type_of% (@padded_native_query_chart)) where
  actual := queryActual
  bridge := Iff.rfl
  variation := ⟨padded_native_query_chart,queryBad,queryBadLaw⟩
  sensitivity := ⟨fun i => ⟨queryBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,queryBadLaw⟩,fun i => nomatch i⟩
  dependence := queryDependence

def queryRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@padded_native_query_chart)
    (type_of% (realize querySignature queryActual.readout queryActual.anchor))
    (LiteralRow → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding.padded_native_query_chart.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding.queryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨queryArena⟩
  objectArena := .source ⟨queryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source queryArena ⟨queryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize querySignature queryActual.readout queryActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding
    definition := none
    coordinates := #[0,2,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","body","arg","body","arg","arg","arg","body","body","arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn","fn","arg","arg"],
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms queryRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding
