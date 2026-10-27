import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicFiniteForcing
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicFiniteForcing
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicFiniteForcing
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature
  (fun _ _ X => @decide (IsFinite X) (Classical.propDecidable _)) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- The single observation is native finiteness; all value and solution clauses stay exact. -/
abbrev arena : Arena where
  signature := signature
  Law A := ∀ {k m r : Nat} (S : FunctionalSystem k m) (mode : Fin k → Bool)
    (R : Fin r → _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.Expr k m),
    (∀ p, satisfies S mode p (canonicalSolution S mode p)) ∧
    ∀ (p : Fin k → Nat) (i : Fin r),
      (A.readout () ()
        (_root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.value
          mode p (canonicalSolution S mode p) (R i)) = true ↔
        i ∈ finiteOriginals S mode R) ∧
      ∀ f, finiteExpressions S mode R i = some f →
        _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.value
          mode p (canonicalSolution S mode p) (R i) = embed (finiteValue p f) ∧
        ∀ v, satisfies S mode p v →
          _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.value
            mode p v (R i) = embed (finiteValue p f)

private theorem actual_law : arena.Law actual := by
  simpa only [arena, actual, realize, decide_eq_true_eq] using (@symbolic_finite_forcing)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let S : FunctionalSystem 0 0 := Fin.elim0
  let mode : Fin 0 → Bool := Fin.elim0
  let p : Fin 0 → Nat := Fin.elim0
  let R : Fin 1 → _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.Expr 0 0 :=
    fun _ => .ground (.of true)
  have mem : (0 : Fin 1) ∈ finiteOriginals S mode R := by
    simp [finiteOriginals, finiteExpressions, symbolic, R]
  have bad := (((law S mode R).2 p 0).1).mpr mem
  exact Bool.noConfusion bad

def evidence : Registration arena (type_of% (@symbolic_finite_forcing)) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), embed (.of true), Omega, ?_⟩
    have finite : IsFinite (embed (.of true)) := ⟨.of true, rfl⟩
    simp only [actual, realize, finite, decide_true,
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.omega_not_finite,
      decide_false, ne_eq, Bool.true_ne_false, not_false_eq_true]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@symbolic_finite_forcing) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicFiniteForcing.symbolic_finite_forcing.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicFiniteForcing.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ X => @decide (IsFinite X) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some CompletionTree
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicFiniteForcing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicFiniteForcing
