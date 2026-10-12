import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address readout)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (History Consistent)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Arith.FibonacciAtomic.Observer

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification

abbrev signature : Signature where
  Params := CutSet
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ Q u => canonicalRow Q u) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P Q : CutSet) (_ : CutPrefixFree P) (_ : CutPrefixFree Q)
    (base : Source) (H : History),
    (analyze (canonicalRow P base) Q H).passes = false →
    ∀ h : Nat, ∃ u v : Source,
      (canonicalRow P u = canonicalRow P base ∧ Consistent H u) ∧
      (canonicalRow P v = canonicalRow P base ∧ Consistent H v) ∧
      (∀ a : Address, a.length ≤ h → readout a u = readout a v) ∧
      R.readout () Q u ≠ R.readout () Q v

theorem bridge : (type_of% (@criterion_failure_arbitrary_depth)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @criterion_failure_arbitrary_depth

def bad : Realization signature := realize signature
  (fun _ _ _ => .of (.inl true)) (fun e => nomatch e)

private theorem root_prefixFree : CutPrefixFree ({[]} : CutSet) := by
  intro p hp q hq
  simp only [Finset.mem_coe, Finset.mem_singleton] at hp hq
  subst p
  subst q
  exact fun _ => rfl

set_option maxHeartbeats 2000000 in
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have failure : (analyze (canonicalRow ({[]} : CutSet) (.of true)) ∅ []).passes = false := by
    let C : LiteralRow := .of (.inr 0)
    let η : NativeHistoryCells.Patterns C 1 := fun _ => .inr ((),())
    have pass : NativeHistoryCells.feasible η [] = true := by
      have law : NativeHistoryCells.syntaxLegal η := by
        intro b c ne
        exfalso
        apply ne
        apply Subtype.ext
        have hb := b.property
        have hc := c.property
        have eb : b.val = 0 := by simpa [C,NativeCutFibers.labels] using hb
        have ec : c.val = 0 := by simpa [C,NativeCutFibers.labels] using hc
        exact eb.trans ec.symm
      simp [NativeHistoryCells.feasible,NativeHistoryCells.testHistory,
        NativeDepthPatterns.Consistent,law]
    by_contra no
    have good : (analyze C ∅ []).passes = true := by
      simpa [C,canonicalRow,literalRow,classOrdinal,firstEqIndex,orderedHoles,reachedHoles,_root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.subtree] using Bool.eq_true_of_not_eq_false no
    have member : η ∈ feasibleList C 1 [] :=
      List.mem_filter.mpr ⟨all_patterns_complete C 1 η,pass⟩
    have all := List.all_eq_true.mp good η member
    have ext : (exteriorVariables (NativeSymbolicRecutting.symbolicExterior ∅ []
        (NativeHistoryCells.wholeTerm η))).isEmpty = true := by
      cases h : (exteriorVariables (NativeSymbolicRecutting.symbolicExterior ∅ []
        (NativeHistoryCells.wholeTerm η))).isEmpty
      · simp [cellPass] at all
        have impossible : (false : Bool) = true := h.symm.trans (congrArg List.isEmpty all.1)
        cases impossible
      · rfl
    change ([⟨⟨0,by simp [C,NativeCutFibers.labels]⟩,Sum.inl ()⟩,
      ⟨⟨0,by simp [C,NativeCutFibers.labels]⟩,Sum.inr ()⟩] : List (NativeHistoryCells.Variables η)).isEmpty = true at ext
    cases ext

  obtain ⟨u,v,hu,hv,same,different⟩ := law {[]} ∅ root_prefixFree
    (by intro p hp; simpa using hp) (.of true) [] failure 0
  exact different rfl

def proof : Registration arena (type_of% (@criterion_failure_arbitrary_depth)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨∅, .of true, .of false, ?_⟩
    change (FreeMagma.of (.inl true) : LiteralRow) ≠ .of (.inl false)
    intro eq
    cases eq

noncomputable def criterion_failure_arbitrary_depth_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification.criterion_failure_arbitrary_depth)
    (Realization signature) ((P Q : CutSet) → CutPrefixFree P → CutPrefixFree Q → Source → History → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification.criterion_failure_arbitrary_depth
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ Q u => canonicalRow Q u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun (_ _ : CutSet) (_ : CutPrefixFree _) (_ : CutPrefixFree _) (_ : Source) (_ : History) => Source)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification
    definition := none
    coordinates := #[0,1,2,3,4,5]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
#print axioms criterion_failure_arbitrary_depth_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification
