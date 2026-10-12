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

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
