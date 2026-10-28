import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedFreeExtension
import Reg.Support.DependentFamily

/-! Satisfaction of the entire guarded system is observed on its completed
state tuple, with the original arbitrary boundary assignment retained. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedFreeExtension

noncomputable section

abbrev signature : Signature where
  Params := Σ k : Nat, Σ m : Nat, System k m × (Fin k → Nat)
  State q := Fin q.2.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature
  (fun _ q v => @decide (Satisfies q.2.2.1 q.2.2.2 v) (Classical.propDecidable _))
  (fun e => nomatch e)

abbrev rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : Nat} (S : System k m) (p : Fin k → Nat), Guarded S →
    ∀ f : Fin m → CompletionTree,
      ∃! v, R.readout () ⟨k, m, S, p⟩ v = true ∧ Extends S f v

private theorem actual_law : arena.Law actual := by
  simpa only [arena, actual, realize, decide_eq_true_eq] using (@guarded_extension)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨v, hv, _⟩ := h (Fin.elim0 : System 0 0) Fin.elim0
    (by intro i; exact Fin.elim0 i) Fin.elim0
  exact Bool.noConfusion hv.1

private theorem readout_depends : ObservationalDependence signature actual := by
  intro role
  let S : System 0 1 := fun _ => some (.ground (.of true))
  let p : Fin 0 → Nat := Fin.elim0
  let v : Fin 1 → CompletionTree := fun _ => leaf true
  let w : Fin 1 → CompletionTree := fun _ => leaf false
  have good : Satisfies S p v := by
    intro i E eq
    have h : E = .ground (.of true) := (Option.some.inj eq).symm
    subst E
    rfl
  have bad : ¬ Satisfies S p w := by
    intro sat
    have eq := sat 0 (.ground (.of true)) rfl
    have tag := congrArg (fun X => (PFunctor.M.dest X).1) eq
    cases tag
  refine ⟨⟨0, 1, S, p⟩, v, w, ?_⟩
  simp only [actual, realize, good, bad, decide_true, decide_false]
  decide

def evidence : Registration arena (type_of% (@guarded_extension)) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@guarded_extension) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension.guarded_extension.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedFreeExtension.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedFreeExtension
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedFreeExtension
