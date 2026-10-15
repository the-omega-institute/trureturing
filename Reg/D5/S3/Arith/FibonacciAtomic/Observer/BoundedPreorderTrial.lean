import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source substitution)
open Observer.BoundedPreorderTrial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Source) (fun _ => Source)

def actual : Realization signature :=
  realize signature (fun _ _ y => y) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => .of true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (h τ start : Nat) (u y : Source),
    u.length = h → y = substitution^[τ] u → start ≤ τ →
    (∀ N, N ≤ τ → TrialSpec h τ N u (R.readout () () y)) ∧
    (∀ N, Attempts start (fun k => Completes h (virtualSource u τ k)) N → N ≤ τ) ∧
    ∃ K, start ≤ K ∧ K ≤ τ ∧ Completes h (virtualSource u τ K) ∧
      (∀ N, start ≤ N → N < K → ¬ Completes h (virtualSource u τ N)) ∧
      K-start+1 ≤ τ-start+1 ∧
      (∀ T, τ ≤ T → K-start+1 ≤ T+1) ∧
      (∀ N, start ≤ N → N ≤ K →
        Attempts start (fun k => Completes h (virtualSource u τ k)) N ∧
        TrialSpec h τ N u y)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have spec := (h 1 0 0 (.of false) (.of false) rfl rfl (by decide)).1 0 (by decide)
  have image := spec.image
  change (FreeMagma.of true : Source) = .of false at image
  cases image

def family : Registration arena (type_of% (@bounded_preorder_trial)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bounded_preorder_trial, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_law
  dependence := by
    intro i
    exact ⟨(), .of true, .of false, by intro h; cases h⟩

def bounded_preorder_trial_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_preorder_trial) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial
