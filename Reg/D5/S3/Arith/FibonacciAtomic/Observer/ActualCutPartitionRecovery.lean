import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery

abbrev valueSignature : Signature where
  Params := CutSet × Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def valueActual : Realization valueSignature := realize valueSignature
  (fun _ p u => classValue p.1 u (classOrdinal p.1 u p.2)) (fun e => nomatch e)
def valueBad : Realization valueSignature := realize valueSignature
  (fun _ _ _ => .of true) (fun e => nomatch e)
abbrev valueArena : Arena where
  signature := valueSignature
  Law R := ∀ (P : CutSet) (_ : CutPrefixFree P) (u : Source) (p : Address) (t : Source)
    (_ : p ∈ P) (_ : subtree p u = some t), R.readout () (P,p) u = t

private theorem root_pf : CutPrefixFree ({[]} : CutSet) := by
  intro a ha b hb hp
  have aa : a = [] := by simpa using ha
  have bb : b = [] := by simpa using hb
  exact aa.trans bb.symm

private theorem value_bad : ¬ valueArena.Law valueBad := by
  intro h
  have eq := h {[]} root_pf (.of false) [] (.of false) (by simp) rfl
  cases eq

def valueProof : Registration valueArena (type_of% (@classValue_at)) where
  actual := valueActual
  bridge := Iff.rfl
  variation := ⟨classValue_at,valueBad,value_bad⟩
  sensitivity := ⟨fun i => ⟨valueBad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,value_bad⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨({[]},[]),.of true,.of false,?_⟩
    have a := classValue_at {[]} root_pf (.of true) [] (.of true) (by simp) rfl
    have b := classValue_at {[]} root_pf (.of false) [] (.of false) (by simp) rfl
    change classValue {[]} (.of true) (classOrdinal {[]} (.of true) []) ≠
      classValue {[]} (.of false) (classOrdinal {[]} (.of false) [])
    rw [a,b]
    intro eq; cases eq

noncomputable def classValue_at_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery.classValue_at)
    (Realization valueSignature) (Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery.classValue_at
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery.valueProof
  realizationSource := none
  generated := false
  arena := .source ⟨valueArena⟩
  objectArena := .source ⟨valueArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source valueArena ⟨valueProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize valueSignature (fun _ p u => classValue p.1 u (classOrdinal p.1 u p.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Source
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
    definition := none
    coordinates := #[0,3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms valueProof
#print axioms classValue_at_registration

abbrev trieSignature : Signature where
  Params := Σ _n : Nat, Σ _P : CutSet, Σ _a : Address, Address
  State _ := Address → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

def trieActual : Realization trieSignature := realize trieSignature
  (fun _ p f => subtree p.2.2.2 (prefixTrie p.1 p.2.1 p.2.2.1 f)) (fun e => nomatch e)
def trieBad : Realization trieSignature := realize trieSignature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev trieArena : Arena where
  signature := trieSignature
  Law R := ∀ (n : Nat) (P : CutSet) (a r : Address) (f : Address → Source)
    (_ : a ++ r ∈ P) (_ : r.length ≤ n)
    (_ : ∀ s : Address, s.IsPrefix r → s ≠ r → a ++ s ∉ P),
    R.readout () ⟨n,P,a,r⟩ f = some (f (a ++ r))

private theorem trie_bad : ¬ trieArena.Law trieBad := by
  intro law
  have eq := law 0 {[]} [] [] (fun _ => .of true) (by simp) (by simp) (by
    intro s pre ne
    have same := List.prefix_nil.mp pre
    exact (ne same).elim)
  cases eq

def trieProof : Registration trieArena (type_of% (@prefixTrie_at)) where
  actual := trieActual
  bridge := Iff.rfl
  variation := ⟨prefixTrie_at,trieBad,trie_bad⟩
  sensitivity := ⟨fun i => ⟨trieBad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,trie_bad⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,{[]},[],[]⟩,(fun _ => .of true),(fun _ => .of false),?_⟩
    change subtree [] (prefixTrie 0 {[]} [] _) ≠ subtree [] (prefixTrie 0 {[]} [] _)
    simp only [prefixTrie,subtree,Finset.mem_singleton,if_pos rfl]
    intro eq
    cases eq

noncomputable def prefixTrie_at_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prefixTrie_at) (Realization trieSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery.prefixTrie_at.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery.trieProof
  realizationSource := none
  generated := false
  arena := .source ⟨trieArena⟩
  objectArena := .source ⟨trieArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source trieArena ⟨trieProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize trieSignature trieActual.readout trieActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg"],
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
