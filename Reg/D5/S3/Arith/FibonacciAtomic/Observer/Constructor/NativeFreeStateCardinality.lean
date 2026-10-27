import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFreeStateCardinality
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFreeStateCardinality
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFreeStateCardinality

abbrev signature : Signature where
  Params := Unit
  State _ := Nat → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ _ s => streamTree s) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => leaf true) (fun e => nomatch e)

/-- The entire arbitrary-stream law and all countable source domains are retained. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ s, R.readout () () s = node (R.readout () () (tail s)) (leaf (!(s 0)))) ∧
    (∀ s j, subtree (bitAddress j) (R.readout () () s) = some (leaf (!(s j)))) ∧
    Function.Injective (R.readout () ()) ∧
    (∀ s, R.readout () () s ≠ Omega) ∧
    (∀ (A : Type) [Countable A] (decode : A → CompletionTree),
      ¬ Function.Surjective decode)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have eq := h.2.2.1 (a₁ := fun _ => false) (a₂ := fun _ => true) rfl
  have bad := congrFun eq 0
  cases bad

def evidence : Registration arena (type_of% free_state_cardinality) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨free_state_cardinality, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (fun _ => false), (fun _ => true), ?_⟩
    intro h
    have eq := free_state_cardinality.2.2.1 h
    have bad := congrFun eq 0
    cases bad

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    free_state_cardinality (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFreeStateCardinality.free_state_cardinality
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFreeStateCardinality.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => streamTree s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFreeStateCardinality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFreeStateCardinality
