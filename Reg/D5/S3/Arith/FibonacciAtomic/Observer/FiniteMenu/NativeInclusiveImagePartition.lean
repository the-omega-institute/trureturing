import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeInclusiveImagePartition
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeInclusiveImagePartition
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (readout Reply)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery (evaluateRow canonicalRow)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers (Classes extend)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage (Image)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation (evaluate)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeInclusiveImagePartition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := NativeSixSourceCones.Fiber
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Classes currentRow → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ u => sourceValues u) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => sourceValues (NativeSixSourceCones.actual 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Q H : Type} [Fintype Q] [Fintype H]
    (M : NativeSixSourceMoore.Controller Q H) (e₀ e₁ : Q ⊕ H)
    (_entriesDistinct : e₀ ≠ e₁) (L : Nat),
    let b := relativeDepth M
    currentRow = NativeSixSourceCones.row ∧
    Fintype.card (Classes currentRow) = 6 ∧
    Finite (Retained currentRow b) ∧
    (∀ (η : Profiles currentRow b) (v : Variables η → BranchImage),
      Image (evaluate (fun x => (v x).val) (wholeTerm η)) ↔ J (wholeTerm η)) ∧
    (∀ u : NativeSixSourceCones.Fiber,
      evaluateRow (extend currentRow (R.readout () () u)) currentRow = substitution u.val ∧
      (profile b u).val = (fun d => expose b (sourceValues u d)) ∧
      (∀ d : Classes currentRow,
        subtree (NativeWholeRowService.representative currentRow d) (substitution u.val) =
          some (sourceValues u d)) ∧
      point (profile b u) (partitionEquiv b u).2 = u) ∧
    (∀ (η : Retained currentRow b) (v : Valuations η),
      partitionEquiv b (point η v) = ⟨η,v⟩ ∧
      substitution (point η v).val =
        evaluateRow (extend currentRow (oldValues η.val (fun x => (v.val x).val))) currentRow ∧
      ∀ (d : Classes currentRow) (x : Frontier (η.val d)),
        subtree (address (η.val d) x) (sourceValues (point η v) d) =
          some (v.val ⟨d,x⟩).val) ∧
    (∀ η : Retained currentRow b,
      Nonempty (Cell η) ∧
      (IsEmpty (Variables η.val) → ∃! u : NativeSixSourceCones.Fiber, profile b u = η) ∧
      (Nonempty (Variables η.val) → ∃ f : Nat → Cell η, Function.Injective f) ∧
      Countable (Cell η) ∧
      ∀ u : NativeSixSourceCones.Fiber, profile b u = η →
        (∀ q : Q, readout (M.addr q) (substitution u.val) = cellReplies M η q) ∧
        canonicalRow NativeSixSourceCones.P u.val = cellTarget η ∧
        (Good M e₀ L u ↔ cellGood M e₀ L η) ∧
        (Good M e₁ L u ↔ cellGood M e₁ L η))

private def emptyMachine : NativeSixSourceMoore.Controller Empty Bool where
  addr e := nomatch e
  next e := nomatch e
  out _ := .of (.inl false)

private theorem image_distinct :
    substitution (NativeSixSourceCones.actual 0).val ≠
      substitution (NativeSixSourceCones.actual 2).val := by
  intro eq
  have reply := congrArg (readout [false,false,true]) eq
  change readout [false,false,true] (substitution (NativeSixSourceCones.origin 0)) =
    readout [false,false,true] (substitution (NativeSixSourceCones.origin 2)) at reply
  rw [(NativeSixSourceCones.six_source_realization.1 0).1,
    (NativeSixSourceCones.six_source_realization.1 2).1] at reply
  change Reply.branch = Reply.alpha at reply
  cases reply

private theorem actual_law : arena.Law actual := @finite_exact_native_partition

private theorem reconstruct (u : NativeSixSourceCones.Fiber) :
    evaluateRow (extend currentRow (sourceValues u)) currentRow = substitution u.val :=
  ((actual_law emptyMachine (.inr false) (.inr true) (by decide) 0).2.2.2.2.1 u).1

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have broken := ((law emptyMachine (.inr false) (.inr true) (by decide) 0).2.2.2.2.1
    (NativeSixSourceCones.actual 2)).1
  exact image_distinct ((reconstruct (NativeSixSourceCones.actual 0)).symm.trans broken)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),NativeSixSourceCones.actual 0,NativeSixSourceCones.actual 2,?_⟩
  intro eq
  have h := congrArg (fun v => evaluateRow (extend currentRow v) currentRow) eq
  exact image_distinct ((reconstruct (NativeSixSourceCones.actual 0)).symm.trans
    (h.trans (reconstruct (NativeSixSourceCones.actual 2))))

def family : Registration arena (type_of% (@finite_exact_native_partition)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_exact_native_partition)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeInclusiveImagePartition.finite_exact_native_partition.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeInclusiveImagePartition.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeInclusiveImagePartition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "arg","arg","arg","arg","fn","arg","body","fn","arg","fn","arg","fn","arg","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeInclusiveImagePartition
