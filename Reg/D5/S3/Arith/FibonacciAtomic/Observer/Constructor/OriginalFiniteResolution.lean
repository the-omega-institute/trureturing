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

abbrev Parameters := Σ k : Nat, Σ m : Nat, Σ _ : Definitions k m, Fin k → Bool

abbrev signature : Signature where
  Params := Parameters
  State p := Expr p.1 p.2.1
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (FiniteExpr p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ p e => compile p.2.2.1 p.2.2.2 e) (fun e => nomatch e)

abbrev rejectedZero : Realization signature :=
  realize signature (fun i p e => if i = 0 then none else compile p.2.2.1 p.2.2.2 e)
    (fun e => nomatch e)

abbrev rejectedOne : Realization signature :=
  realize signature (fun i p e => if i = 1 then some (.ground (.of false)) else
    compile p.2.2.1 p.2.2.2 e) (fun e => nomatch e)

/-- The original telescope and both compiler occurrences are retained. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k m : Nat) (E : Definitions k m) (mode : Fin k → Bool),
    (∀ e : Expr k m, (R.readout 0 ⟨k, m, E, mode⟩ e).isSome = true ↔
      FiniteDerivation E mode e) ∧
    (∀ (e : Expr k m) (f : FiniteExpr k), R.readout 1 ⟨k, m, E, mode⟩ e = some f →
      ∀ (p : Fin k → Nat) (v : Fin m → CompletionTree),
        Solution E mode p v → value mode p v e = embed (finiteValue p f))

private theorem rejected_zero_fails : ¬ arena.Law rejectedZero := by
  intro h
  have fail := (h 0 0 Fin.elim0 Fin.elim0).1 (.ground (.of true))
  have good : FiniteDerivation (k := 0) (m := 0) Fin.elim0 Fin.elim0
      (.ground (.of true)) := .ground _
  have : (none : Option (FiniteExpr 0)).isSome = true := fail.mpr good
  cases this

private theorem rejected_one_fails : ¬ arena.Law rejectedOne := by
  intro h
  have eq := (h 0 0 Fin.elim0 Fin.elim0).2 (.ground (.of true)) (.ground (.of false))
    rfl Fin.elim0 Fin.elim0 (by intro i; exact i.elim0)
  have he := congrArg (fun X => (PFunctor.M.dest X).1) eq
  have bad : (true : Bool) = false := Sum.inl.inj (by
    simpa only [value, finiteValue, embed, leaf, PFunctor.M.dest_mk] using he)
  cases bad

abbrev Statement : Prop := ∀ (k m : Nat) (E : Definitions k m) (mode : Fin k → Bool),
  (∀ e : Expr k m, (compile E mode e).isSome = true ↔ FiniteDerivation E mode e) ∧
  (∀ (e : Expr k m) (f : FiniteExpr k), compile E mode e = some f →
    ∀ (p : Fin k → Nat) (v : Fin m → CompletionTree), Solution E mode p v →
      value mode p v e = embed (finiteValue p f))

def familyRegistration : Registration arena Statement := by
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨original_finite_resolution, rejectedZero, rejected_zero_fails⟩
    sensitivity := ⟨?_, fun e => nomatch e⟩
    dependence := ?_ }
  · intro i
    fin_cases i
    · refine ⟨rejectedZero, ?_, rfl, rejected_zero_fails⟩
      intro j hj
      funext p e
      simp only [actual, rejectedZero, realize, if_neg hj]
    · refine ⟨rejectedOne, ?_, rfl, rejected_one_fails⟩
      intro j hj
      funext p e
      simp only [actual, rejectedOne, realize, if_neg hj]
  · intro i
    refine ⟨⟨0, 0, Fin.elim0, Fin.elim0⟩, .ground (.of true), .ground (.of false), ?_⟩
    intro h
    have groundEq : (FreeMagma.of true : FreeMagma Bool) = .of false := by
      simpa [actual, realize, compile, resolve] using h
    cases groundEq

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    original_finite_resolution
    (type_of% (realize signature (fun _ p e => compile p.2.2.1 p.2.2.2 e)
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
  readout := some (realize signature (fun _ p e => compile p.2.2.1 p.2.2.2 e)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalFiniteResolution
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg", "body", "body", "domain", "fn", "arg", "fn"]
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
