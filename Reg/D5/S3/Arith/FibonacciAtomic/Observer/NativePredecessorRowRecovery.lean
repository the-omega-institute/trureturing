import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery

abbrev signature : Signature where
  Params := CutSet
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => back (canonicalRow p (substitution v)) (H p v))
  (fun e => nomatch e)

def bad : Realization signature := realize signature (fun _ _ _ => none) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : CutSet) (hP : CutPrefixFree P),
    (∀ v : Source, R.readout () P v = some (canonicalRow P v)) ∧
    (∀ v w : Source, canonicalRow P (substitution v) = canonicalRow P (substitution w) →
      (canonicalRow P v = canonicalRow P w ↔ H P v = H P w))

theorem bridge : (type_of% (@native_predecessor_row_recovery)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @native_predecessor_row_recovery

private theorem empty_prefixFree : CutPrefixFree (∅ : CutSet) := by
  intro p hp
  simp at hp

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have eq := (law ∅ empty_prefixFree).1 (.of true)
  change none = some (canonicalRow ∅ (.of true)) at eq
  cases eq

def proof : Registration arena (type_of% (@native_predecessor_row_recovery)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨∅,.of true,.of false,?_⟩
    intro eq
    have alpha := (actual_law ∅ empty_prefixFree).1 (.of true)
    have beta := (actual_law ∅ empty_prefixFree).1 (.of false)
    have role : i = () := Subsingleton.elim _ _
    rw [role, alpha, beta] at eq
    have rows := Option.some.inj eq
    change (FreeMagma.of (.inl true) : LiteralRow) = .of (.inl false) at rows
    cases rows

noncomputable def native_predecessor_row_recovery_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery.native_predecessor_row_recovery)
    (Realization signature) ((P : CutSet) → CutPrefixFree P → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery.native_predecessor_row_recovery
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery.proof
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
    (fun _ p v => back (canonicalRow p (substitution v)) (H p v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
#print axioms native_predecessor_row_recovery_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery
