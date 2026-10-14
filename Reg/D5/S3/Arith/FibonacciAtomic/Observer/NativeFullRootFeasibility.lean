import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery (H back)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : CutSet, Source
  State p := Classes (canonicalRow p.1 (substitution p.2)) → Option Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CutSet
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p θ => oldMask (canonicalRow p.1 (substitution p.2)) θ) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : CutSet) (_ : CutPrefixFree P) (u₀ : Source) (r q : Nat) (_ : 1 ≤ r),
    let C := canonicalRow P (substitution u₀)
    (∀ (v : ImageValues C) (u : OriginFiber P C),
      substitution u.val = evaluateRow (extend C v.val.val) C →
      R.readout () ⟨P,u₀⟩ (types C v.val.val) = H P u.val ∧
      back C (oldMask C (types C v.val.val)) = some (canonicalRow P u.val) ∧
      target C (types C v.val.val) = canonicalRow P u.val) ∧
    (∀ θ : Chart C, ∃ row : LiteralRow, back C (oldMask C θ.val) = some row) ∧
    (∀ (v : ImageValues C) (d : Classes C),
      subtree (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.representative C d)
        (evaluateRow (extend C v.val.val) C) = some (v.val.val d) ∧
      readout (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.representative C d)
        (evaluateRow (extend C v.val.val) C) =
          _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding.rootReply (types C v.val.val d)) ∧
    (InvFeas P C r q ↔ RootFeas C r q)

private theorem badLaw : ¬ arena.Law bad := by
  classical
  intro h
  have hp : CutPrefixFree {[]} := by
    intro a ha b hb _
    change a ∈ ({[]} : CutSet) at ha
    change b ∈ ({[]} : CutSet) at hb
    simp only [Finset.mem_singleton] at ha hb
    exact ha.trans hb.symm
  let C := canonicalRow {[]} (substitution (.of true))
  let w : RowFiber {[]} C := ⟨substitution (.of true),rfl⟩
  let v : ImageValues C := ⟨recover {[]} hp C w,⟨.of true,(recover_fill {[]} hp C w).symm⟩⟩
  have image : substitution (.of true) = evaluateRow (extend C v.val.val) C :=
    (recover_fill {[]} hp C w).symm
  have eq := (h {[]} hp (.of true) 1 0 (by decide)).1 v ⟨.of true,rfl⟩ image |>.1
  change (∅ : CutSet) = H {[]} (.of true) at eq
  have member := congrArg (fun s : CutSet => ([] : Address) ∈ s) eq
  simpa [H,canonicalRow,literalRow,holeAddresses] using member

private theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  let P : CutSet := {[true]}
  let u₀ : Source := .mul (.of true) (.of true)
  let C := canonicalRow P (substitution u₀)
  have row : C = .mul (.of (.inl false)) (.of (.inr 0)) := by
    simp [C,P,u₀,canonicalRow,literalRow,substitution.map_mul,substitution,
      classOrdinal,firstEqIndex,orderedHoles,reachedHoles,subtree]
  let α : Classes C → Option Bool := fun _ => some true
  let β : Classes C → Option Bool := fun _ => some false
  have absent : [true] ∉ oldMask C α := by
    intro hm
    have no := (Finset.mem_filter.mp hm).2
    apply no
    refine ⟨[],true,rfl,?_⟩
    refine ⟨.of (.inr 0),?_,?_⟩
    · simp [row,rowAt]
    · simp [lit,typeExtend,α,row,labels]
  have present : [true] ∈ oldMask C β := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · simp [row,holeAddresses]
    · rintro ⟨q,d,eq,ha⟩
      have len := congrArg List.length eq
      have qnil : q = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp only [List.length_append,List.length_singleton] at len
        omega
      subst q
      rcases ha with ⟨e,he,ha⟩
      have ee : e = .of (.inr 0) := by simpa [row,rowAt] using he.symm
      subst e
      simpa [lit,typeExtend,β,row,labels] using ha
  refine ⟨⟨P,u₀⟩,α,β,?_⟩
  intro eq
  change oldMask C α = oldMask C β at eq
  exact absent (eq.symm ▸ present)

def family : Registration arena (type_of% (@native_full_root_feasibility)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_full_root_feasibility,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_full_root_feasibility)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility.native_full_root_feasibility.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg",
        "body","body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
