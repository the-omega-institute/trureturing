import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence

abbrev signature : Signature where
  Params := CompletionTree
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ t => embed t) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => leaf false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ T : CompletionTree, (¬ ∃ t : Source, R.readout () T t = T) → HasInfiniteBranch T

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have absent_finite : ¬ ∃ t : Source, bad.readout () (leaf true) t = leaf true := by
    rintro ⟨t, ht⟩
    have no := congrArg (completionReadout []) ht
    change Reply.beta = Reply.alpha at no
    cases no
  obtain ⟨b, branch⟩ := law (leaf true) absent_finite
  have no := branch 1
  simp [List.ofFn_succ, completionReadout, leaf] at no

def proof : Registration arena (type_of% (@infinite_of_not_finite)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨infinite_of_not_finite, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, bad_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨leaf true, .of true, .of false, ?_⟩
    intro h
    have no := congrArg (completionReadout []) h
    change Reply.alpha = Reply.beta at no
    cases no

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence.infinite_of_not_finite)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence.infinite_of_not_finite
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => embed t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","domain","arg","arg","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence
