import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalFiniteResolution
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.OriginalFiniteResolution
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion (Expr value)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalFiniteResolution
noncomputable section

structure Parameters where
  k : Nat
  m : Nat
  definitions : Definitions k m
  mode : Fin k → Bool

abbrev signature : Signature where
  Params := Parameters
  State p := Expr p.k p.m
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (FiniteExpr p.k)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ p e => compile p.definitions p.mode e) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : Parameters,
    (∀ e : Expr q.k q.m, (R.readout () q e).isSome = true ↔
      FiniteDerivation q.definitions q.mode e) ∧
    (∀ (e : Expr q.k q.m) (f : FiniteExpr q.k), R.readout () q e = some f →
      ∀ (p : Fin q.k → Nat) (v : Fin q.m → CompletionTree),
        Solution q.definitions q.mode p v → value q.mode p v e = embed (finiteValue p f))

private def emptyParameters : Parameters := ⟨0, 0, Fin.elim0, Fin.elim0⟩

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have fail := (h emptyParameters).1 (.ground (.of true))
  have good : FiniteDerivation emptyParameters.definitions emptyParameters.mode
      (.ground (.of true)) := .ground _
  have : (none : Option (FiniteExpr 0)).isSome = true := fail.mpr good
  cases this

abbrev Statement : Prop := ∀ (k m : Nat) (E : Definitions k m) (mode : Fin k → Bool),
  (∀ e : Expr k m, (compile E mode e).isSome = true ↔ FiniteDerivation E mode e) ∧
  (∀ (e : Expr k m) (f : FiniteExpr k), compile E mode e = some f →
    ∀ (p : Fin k → Nat) (v : Fin m → CompletionTree), Solution E mode p v →
      value mode p v e = embed (finiteValue p f))

def familyRegistration : Registration arena Statement := by
  have positive : arena.Law actual := fun p =>
    original_finite_resolution p.k p.m p.definitions p.mode
  refine {
    actual := actual
    bridge := ⟨fun h p => h p.k p.m p.definitions p.mode,
      fun h k m E b => h ⟨k, m, E, b⟩⟩
    variation := ⟨positive, rejected, rejected_fails⟩
    sensitivity := ⟨?_, fun e => nomatch e⟩
    dependence := ?_ }
  · intro i
    exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_fails⟩
  · intro i
    refine ⟨emptyParameters, .ground (.of true), .ground (.of false), ?_⟩
    intro h
    have groundEq : (true : Bool) = false := by
      simpa [actual, realize, compile, resolve] using h
    cases groundEq

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    original_finite_resolution
    (type_of% (realize signature (fun _ p e => compile p.definitions p.mode e)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalFiniteResolution.original_finite_resolution
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalFiniteResolution.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p e => compile p.definitions p.mode e)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalFiniteResolution
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalFiniteResolution
