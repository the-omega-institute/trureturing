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

namespace ActualType
abbrev signature : Signature where
  Params := Σ _ : CutSet, Source
  State p := ImageValues (canonicalRow p.1 p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Classes (canonicalRow p.1 p.2) → Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => types (canonicalRow p.1 p.2) v.val.val) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ _ => some true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : CutSet) (_ : CutPrefixFree P) (t₀ : Source)
    (v : ImageValues (canonicalRow P t₀)),
    Admissible (canonicalRow P t₀) (R.readout () ⟨P,t₀⟩ v)

private theorem root_prefix : CutPrefixFree {[]} := by
  intro a ha b hb _
  change a ∈ ({[]} : CutSet) at ha
  change b ∈ ({[]} : CutSet) at hb
  simp only [Finset.mem_singleton] at ha hb
  exact ha.trans hb.symm
private def row : LiteralRow := canonicalRow {[]} (.of false)
private theorem row_eq : row = .of (.inr 0) := by
  simp [row,canonicalRow,literalRow,classOrdinal,firstEqIndex,orderedHoles,reachedHoles,subtree]
private def values (u : Source) : ImageValues row :=
  ⟨⟨fun _ => substitution u,by
    intro a b _
    apply Subtype.ext
    have ha := a.property
    have hb := b.property
    simp [row_eq,labels] at ha hb
    exact ha.trans hb.symm⟩,⟨u,by simp [row_eq,evaluateRow,extend,labels]⟩⟩
private theorem badLaw : ¬ arena.Law bad := by
  intro h
  have hh := (h {[]} root_prefix (.of false) (values (.of true))).1
  change im (typeExtend row (fun _ => some true)) row at hh
  simpa [row_eq,im,typeExtend,labels] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨{[]},.of false⟩,values (.of true),values (.of false),?_⟩
  intro he
  let d : Classes row := ⟨0,by simp [row_eq,labels]⟩
  have hd := congrFun he d
  change rootType (substitution (.of true)) = rootType (substitution (.of false)) at hd
  cases hd

def family : Registration arena (type_of% (@actual_type)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_type,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_type)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility.actual_type.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility.ActualType.family
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
      path := #["body","body","body","body","arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end ActualType

namespace InstallCorrect
abbrev signature : Signature where
  Params := Σ C : LiteralRow, Σ _ : LiteralRow, RootTree C LiteralRow
  State p := Classes p.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow × Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => nativeRun (fun a => readout a (evaluateRow (extend p.1 v) p.1))
    (install p.1 p.2.1 p.2.2)) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => (.of (.inl true),0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (C : LiteralRow) (fallback : LiteralRow) (T : RootTree C LiteralRow)
    (v : Classes C → Source),
    R.readout () ⟨C,fallback,T⟩ v = rootRun (types C v) T ∧
      nativeDepth (install C fallback T) = rootDepth T
private def zero : LiteralRow := .of (.inl false)
private theorem badLaw : ¬ arena.Law bad := by
  intro h
  have hh := (h zero zero (.stop zero) (fun _ => .of false)).1
  change ((FreeMagma.of (Sum.inl true) : LiteralRow),0) = (zero,0) at hh
  have ho := congrArg Prod.fst hh
  cases ho
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let C : LiteralRow := .of (.inr 0)
  let d : Classes C := ⟨0,by simp [C,labels]⟩
  let T : RootTree C LiteralRow := .ask d (.stop zero) (.stop (.of (.inl true))) (.stop zero)
  let v : Classes C → Source := fun _ => .of true
  let w : Classes C → Source := fun _ => .of false
  refine ⟨⟨C,zero,T⟩,v,w,?_⟩
  intro he
  change nativeRun (fun a => readout a (evaluateRow (extend C v) C)) (install C zero T) =
    nativeRun (fun a => readout a (evaluateRow (extend C w) C)) (install C zero T) at he
  rw [(install_correct C zero T v).1,(install_correct C zero T w).1] at he
  have ho := congrArg Prod.fst he
  change (FreeMagma.of (Sum.inl false) : LiteralRow) = .of (.inl true) at ho
  cases ho

def family : Registration arena (type_of% (@install_correct)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨install_correct,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@install_correct)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility.install_correct.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility.InstallCorrect.family
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
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end InstallCorrect

namespace DialogueRun
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization (Dialogue)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine (Run answers)
abbrev signature : Signature where
  Params := Dialogue LiteralRow
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ T t => (nativeRun (fun a => readout a t) T).1) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .of (.inl true)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (T : Dialogue LiteralRow) (t : Source),
    ∃ tr, Run controller T 0 t tr (R.readout () T t) ∧
      Stationary tr ∧ (answers tr).length = (nativeRun (fun a => readout a t) T).2
private def zero : LiteralRow := .of (.inl false)
private theorem badLaw : ¬ arena.Law bad := by
  intro h
  obtain ⟨tr,run,_,_⟩ := h (.stop zero) (.of true)
  cases run <;> simp_all [controller,bad,realize,zero]
  rename_i he
  cases he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let T : Dialogue LiteralRow := .read [] (.stop zero) (.stop (.of (.inl true)))
    (.stop zero) (.stop zero)
  refine ⟨T,.of true,.of false,?_⟩
  intro he
  change (FreeMagma.of (Sum.inl false) : LiteralRow) = .of (.inl true) at he
  cases he

def family : Registration arena (type_of% (@dialogue_run)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dialogue_run,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dialogue_run)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility.dialogue_run.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility.DialogueRun.family
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
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","arg","body","fn","arg","arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end DialogueRun

namespace NativeCalls
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization (Dialogue)
abbrev signature : Signature where
  Params := Dialogue LiteralRow
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ T t => (nativeRun (fun a => readout a t) T).2) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ T _ => nativeDepth T + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (T : Dialogue LiteralRow) (t : Source),
    R.readout () T t ≤ nativeDepth T
private def zero : LiteralRow := .of (.inl false)
private theorem badLaw : ¬ arena.Law bad := by
  intro h
  have hh := h (.stop zero) (.of true)
  change 1 ≤ 0 at hh
  exact (by decide : ¬ (1 ≤ 0)) hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let Z : Dialogue LiteralRow := .stop zero
  let A : Dialogue LiteralRow := .read [] Z Z Z Z
  let T : Dialogue LiteralRow := .read [] Z A Z Z
  refine ⟨T,.of true,.of false,?_⟩
  intro he
  change 1 = 2 at he
  exact (by decide : (1 : Nat) ≠ 2) he

def family : Registration arena (type_of% (@native_calls)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_calls,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_calls)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility.native_calls.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility.NativeCalls.family
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
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end NativeCalls

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
