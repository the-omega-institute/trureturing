import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
open D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization

private def rootTag : Source → Source
  | .of b => .of b
  | .mul _ _ => .mul (.of true) (.of true)

namespace Bounded
abbrev signature : Signature where
  Params := Σ _m : Nat, Σ _M : Nat, Nat
  State p := Fin p.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := MixedExpr (Fin p.1) → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ z => eval z) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ z E => rootTag (eval z E)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m M d : Nat) (A B : MixedExpr (Fin m)),
    weight A ≤ M → weight B ≤ M → decoration A ≤ d → decoration B ≤ d →
    (R.readout () ⟨m,M,d⟩ (separator m M d) A = R.readout () ⟨m,M,d⟩ (separator m M d) B ↔
      ∀ z : Fin m → Source, R.readout () ⟨m,M,d⟩ z A = R.readout () ⟨m,M,d⟩ z B)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  let A : MixedExpr (Fin 1) := .residual 0 0
  let B : MixedExpr (Fin 1) := .ground (comb 1)
  have wa : weight A ≤ 1 := by decide
  have wb : weight B ≤ 1 := by change gamma (comb 1) ≤ 1; rw [gamma_comb]
  have da : decoration A ≤ 0 := by decide
  have db : decoration B ≤ 0 := by decide
  have eq : bad.readout () ⟨1,1,0⟩ (separator 1 1 0) A =
      bad.readout () ⟨1,1,0⟩ (separator 1 1 0) B := by rfl
  have no := (h 1 1 0 A B wa wb da db).mp eq (fun _ => .of true)
  change FreeMagma.of true = FreeMagma.mul (.of true) (.of true) at no
  cases no

def proof : Registration arena (type_of% (@bounded_identity_reflection)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bounded_identity_reflection,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1,0,0⟩,(fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq
    have no := congrFun eq (.residual 0 0)
    cases no

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.bounded_identity_reflection)
    (Realization signature) (Nat → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.bounded_identity_reflection
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.Bounded.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => eval z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","arg","body","fn","arg","fn"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Bounded

namespace Instantiation
abbrev signature : Signature where
  Params := Σ k : Nat, Σ _m : Nat, Fin k → Nat
  State p := Fin p.2.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := MixedExpr (Fin p.2.1) → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ z => eval z) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ z E => rootTag (eval z E)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k m : Nat) (n : Fin k → Nat) (z : Fin m → Source) (E : RankedExpr k m),
    R.readout () ⟨k,m,n⟩ z (instantiate n E) = rankedEval n z E

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have no := h 0 0 (fun i => nomatch i) (fun i => nomatch i)
    (.ground (.mul (.of false) (.of false)))
  change FreeMagma.mul (.of true) (.of true) = FreeMagma.mul (.of false) (.of false) at no
  cases no

def proof : Registration arena (type_of% (@instantiate_eval)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@instantiate_eval,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,1,(fun x => nomatch x)⟩,(fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq
    have no := congrFun eq (.residual 0 0)
    cases no

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.instantiate_eval)
    (Realization signature) (Nat → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.instantiate_eval
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.Instantiation.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => eval z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg","fn"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Instantiation

namespace Uniform
abbrev signature : Signature where
  Params := Σ k : Nat, Σ m : Nat, Σ _pairs : List (RankedExpr k m × RankedExpr k m), Fin k → Nat
  State p := Fin p.2.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := RankedExpr p.1 p.2.1 → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p z => rankedEval p.2.2.2 z) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ p z E => rootTag (rankedEval p.2.2.2 z E)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k m : Nat) (pairs : List (RankedExpr k m × RankedExpr k m))
    (n : Fin k → Nat) (p : RankedExpr k m × RankedExpr k m), p ∈ pairs →
    (R.readout () ⟨k,m,pairs,n⟩ (uniformSeparator pairs) p.1 =
      R.readout () ⟨k,m,pairs,n⟩ (uniformSeparator pairs) p.2 ↔
      ∀ z : Fin m → Source, R.readout () ⟨k,m,pairs,n⟩ z p.1 = R.readout () ⟨k,m,pairs,n⟩ z p.2)

private def A : RankedExpr 0 1 := .residual 0 (.inr 0)
private def B : RankedExpr 0 1 := .ground (comb 1)
private def n : Fin 0 → Nat := fun x => nomatch x

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have eq : bad.readout () ⟨0,1,[(A,B)],n⟩ (uniformSeparator [(A,B)]) A =
      bad.readout () ⟨0,1,[(A,B)],n⟩ (uniformSeparator [(A,B)]) B := by rfl
  have no := (h 0 1 [(A,B)] n (A,B) (by simp)).mp eq (fun _ => .of true)
  change FreeMagma.of true = FreeMagma.mul (.of true) (.of true) at no
  cases no

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,1,[],n⟩,(fun _ => .of true),(fun _ => .of false),?_⟩
  intro eq
  have no := congrFun eq A
  cases no

def proof : Registration arena (type_of% (@uniform_residual_reflection)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_residual_reflection,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.uniform_residual_reflection)
    (Realization signature) (Nat → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.uniform_residual_reflection
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.Uniform.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => rankedEval p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","body","fn","arg","fn"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev completionArena : Arena where
  signature := signature
  Law R := ∀ (k m : Nat) (pairs : List (RankedExpr k m × RankedExpr k m)) (n : Fin k → Nat),
    (∀ p ∈ pairs, ∃ z : Fin m → Source,
      R.readout () ⟨k,m,pairs,n⟩ z p.1 ≠ R.readout () ⟨k,m,pairs,n⟩ z p.2) ↔
      ∀ p ∈ pairs, R.readout () ⟨k,m,pairs,n⟩ (uniformSeparator pairs) p.1 ≠
        R.readout () ⟨k,m,pairs,n⟩ (uniformSeparator pairs) p.2

private theorem completionBad : ¬ completionArena.Law bad := by
  intro h
  have individual : ∀ p ∈ [(A,B)], ∃ z : Fin 1 → Source,
      bad.readout () ⟨0,1,[(A,B)],n⟩ z p.1 ≠ bad.readout () ⟨0,1,[(A,B)],n⟩ z p.2 := by
    intro p hp
    have ep : p = (A,B) := by simpa using hp
    subst p
    exact ⟨(fun _ => .of true),by intro no; cases no⟩
  have no := (h 0 1 [(A,B)] n).mp individual (A,B) (by simp)
  exact no rfl

def completionProof : Registration completionArena (type_of% (@simultaneous_completion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@simultaneous_completion,bad,completionBad⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,completionBad⟩,
    fun i => nomatch i⟩
  dependence := dependence

noncomputable def completionRegistration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.simultaneous_completion)
    (Realization signature) (Nat → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.simultaneous_completion
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization.Uniform.completionProof
  realizationSource := none
  generated := false
  arena := .source ⟨completionArena⟩
  objectArena := .source ⟨completionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source completionArena ⟨completionProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => rankedEval p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","body","body","arg","body","fn","arg","fn"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Uniform

#print axioms Bounded.proof
#print axioms Uniform.proof
#print axioms Uniform.completionProof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
