import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
noncomputable section

abbrev signature : Signature where
  Params := Σ m : Nat, System m × Fin m
  State p := Fin p.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ p v => v p.2.2) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => leaf true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Nat} {S : System m} {v : Fin m → CompletionTree},
    Satisfies S v → ∀ {i : Fin m} (cycle : Walk S i i),
      IsFinite (R.readout () ⟨m, S, i⟩ v) → ¬ cycle.Strict

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let S : System 1 := fun i => some (.var 1 i)
  let v : Fin 1 → CompletionTree := fun _ => Omega
  have sat : Satisfies S v := by
    intro i E eq
    have ee : E = .var 1 i := (Option.some.inj eq).symm
    subst E
    change Omega = rho^[1] Omega
    exact (iterate_omega 1).symm
  let edge : Dependency S 0 0 := {
    expression := .var 1 0
    equation := rfl
    address := []
    power := 1
    occurrence := .var 1 0 }
  let cycle : Walk S 0 0 := .cons edge (.nil 0)
  have negative := law sat cycle ⟨.of true, rfl⟩
  exact negative (Or.inr (Or.inl (by decide)))

def evidence : Registration arena (type_of% (@finite_cycle_is_silent)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_cycle_is_silent, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1, (fun _ => none), 0⟩, (fun _ => leaf true), (fun _ => leaf false), ?_⟩
    intro h
    have root := congrArg (fun X => (PFunctor.M.dest X).1) h
    have hb : (Sum.inl true : Bool ⊕ Unit) = Sum.inl false := by
      simpa only [actual, realize, leaf, PFunctor.M.dest_mk] using root
    cases Sum.inl.inj hb

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_cycle_is_silent) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction.finite_cycle_is_silent.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => v p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "type", "arg"]
      stateBinder := 2
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
