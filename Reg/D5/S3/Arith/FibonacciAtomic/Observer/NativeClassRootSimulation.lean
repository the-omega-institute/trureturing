import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization (Dialogue)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev simulationSignature : Signature where
  Params := Σ P : CutSet, Σ t : Source, Chart (canonicalRow P t)
  State p := RootTree (canonicalRow p.1 p.2.1) LiteralRow
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def simulationActual : Realization simulationSignature := realize simulationSignature
  (fun _ p E => (rootRun p.2.2.val E).1) (fun e => nomatch e)
def simulationBad : Realization simulationSignature := realize simulationSignature
  (fun _ _ _ => .of (.inl false)) (fun e => nomatch e)

abbrev simulationArena : Arena where
  signature := simulationSignature
  Law R := ∀ (P : CutSet) (_ : CutPrefixFree P)
    (t₀ : Source) (S : Type) [Finite S]
    (σ : ImageValues (canonicalRow P t₀) → S) (E : S → Dialogue LiteralRow) (q : Nat)
    (_ : ∀ s, nativeDepth (E s) ≤ q)
    (_ : ∀ (v : ImageValues (canonicalRow P t₀))
      (u : OriginFiber P (canonicalRow P t₀)),
      substitution u.val = evaluateRow (extend (canonicalRow P t₀) v.val.val) (canonicalRow P t₀) →
      (nativeRun (fun a => readout a (substitution u.val)) (E (σ v))).1 = canonicalRow P u.val),
    ∃ (v : Chart (canonicalRow P t₀) → ImageValues (canonicalRow P t₀))
      (u : Chart (canonicalRow P t₀) → OriginFiber P (canonicalRow P t₀))
      (c : Chart (canonicalRow P t₀) → S),
      ∀ θ,
        substitution (u θ).val = evaluateRow (extend (canonicalRow P t₀) (v θ).val.val) (canonicalRow P t₀) ∧
        types (canonicalRow P t₀) (v θ).val.val = θ.val ∧
        c θ = σ (v θ) ∧
        R.readout () ⟨P,t₀,θ⟩ (compileRoot (canonicalRow P t₀) (E (c θ))) = canonicalRow P (u θ).val ∧
        (rootRun θ.val (compileRoot (canonicalRow P t₀) (E (c θ)))).2 ≤
          (nativeRun (fun a => readout a (substitution (u θ).val)) (E (σ (v θ)))).2 ∧
        rootDepth (compileRoot (canonicalRow P t₀) (E (c θ))) ≤ q

private theorem root_row (t : Source) : canonicalRow {[]} t = .of (.inr 0) := by
  cases t <;> simp [canonicalRow,literalRow,classOrdinal,orderedHoles,reachedHoles,firstEqIndex,
    _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.subtree]

theorem simulationBadLaw : ¬ simulationArena.Law simulationBad := by
  intro h
  have hp : CutPrefixFree {[]} := by
    intro a ha b hb _
    have ha : a = [] := by simpa using ha
    have hb : b = [] := by simpa using hb
    exact ha.trans hb.symm
  have hc := root_row (.of false)
  have ha : Admissible (canonicalRow {[]} (.of false)) (fun _ => some false) := by
    rw [hc]
    simp [Admissible,im,typeExtend,labels]
    decide
  have correct : ∀ (v : ImageValues (canonicalRow {[]} (.of false)))
      (u : OriginFiber {[]} (canonicalRow {[]} (.of false))),
      substitution u.val = evaluateRow (extend (canonicalRow {[]} (.of false)) v.val.val)
        (canonicalRow {[]} (.of false)) →
      (nativeRun (fun a => readout a (substitution u.val))
        (Dialogue.stop (.of (.inr 0)))).1 = canonicalRow {[]} u.val := by
    intro v u _
    exact (root_row u.val).symm
  obtain ⟨v,u,c,out⟩ := h {[]} hp (.of false) Unit (fun _ => ())
    (fun _ => .stop (.of (.inr 0))) 0 (fun _ => Nat.le_refl 0) correct
  have eq := (out ⟨fun _ => some false,ha⟩).2.2.2.1
  change FreeMagma.of (Sum.inl false) = canonicalRow {[]} _ at eq
  rw [root_row] at eq
  cases eq

theorem simulationDependence : ObservationalDependence simulationSignature simulationActual := by
  intro i
  have ha : Admissible (canonicalRow ∅ (.of false)) (fun _ => none) := by
    simp [canonicalRow,literalRow,Admissible,im]
    decide
  refine ⟨⟨∅,.of false,⟨fun _ => none,ha⟩⟩,.stop (.of (.inl true)),.stop (.of (.inl false)),?_⟩
  intro h
  change FreeMagma.of (Sum.inl true) = FreeMagma.of (Sum.inl false) at h
  cases h

def simulationFamily : Registration simulationArena (type_of% (@truthful_joint_root_simulation)) where
  actual := simulationActual
  bridge := Iff.rfl
  variation := ⟨truthful_joint_root_simulation,simulationBad,simulationBadLaw⟩
  sensitivity := ⟨fun i => ⟨simulationBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,simulationBadLaw⟩,fun i => nomatch i⟩
  dependence := simulationDependence

def simulationRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@truthful_joint_root_simulation)
    (type_of% (realize simulationSignature simulationActual.readout simulationActual.anchor))
    (RootTree (.of (.inl false)) LiteralRow → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation.truthful_joint_root_simulation.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation.simulationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨simulationArena⟩
  objectArena := .source ⟨simulationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source simulationArena ⟨simulationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize simulationSignature simulationActual.readout simulationActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
    definition := none
    coordinates := #[0,2,13]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","arg","body","arg","body","arg","body","body","arg","arg","arg","fn","arg","fn","arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg","arg"],
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms simulationRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
