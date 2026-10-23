import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
open D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (Pattern Frontier decompose)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation

abbrev signature : Signature where
  Params := Σ k : Nat, Σ r : Nat, Σ m : Nat,
    Σ _pairs : List (RankedExpr k (r+m) × RankedExpr k (r+m)),
    Σ _P : (Fin k → Nat) → Prop, Σ _n : Fin k → Nat, Σ _f : Fin r → Source,
    Σ d : Fin m → Nat, (i : Fin m) → Pattern (d i)
  State p := Fin p.2.2.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := RankedExpr p.1 (p.2.1+p.2.2.1) → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p z => fixedEval p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 z) (fun e => nomatch e)

private def rootTag : Source → Source
  | .of b => .of b
  | .mul _ _ => .mul (.of true) (.of true)

def bad : Realization signature := realize signature
  (fun _ p z E => rootTag (fixedEval p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 z E))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k r m : Nat)
    (pairs : List (RankedExpr k (r+m) × RankedExpr k (r+m)))
    (P : (Fin k → Nat) → Prop) (n : Fin k → Nat) (f : Fin r → Source)
    (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i)),
    (∀ i, Nonempty (Frontier (p i))) →
    ((∃ z : Fin m → Source, P n ∧ ∀ e ∈ pairs,
      R.readout () ⟨k,r,m,pairs,P,n,f,d,p⟩ z e.1 ≠ R.readout () ⟨k,r,m,pairs,P,n,f,d,p⟩ z e.2) ↔
    P n ∧ (∀ i, (decompose (d i) (prefixTuple n f d p pairs i)).1 = p i) ∧
      ∀ e ∈ pairs, R.readout () ⟨k,r,m,pairs,P,n,f,d,p⟩ (prefixTuple n f d p pairs) e.1 ≠
        R.readout () ⟨k,r,m,pairs,P,n,f,d,p⟩ (prefixTuple n f d p pairs) e.2)

private def n : Fin 0 → Nat := fun x => nomatch x
private def f : Fin 0 → Source := fun x => nomatch x
private def d : Fin 1 → Nat := fun _ => 1
private def p : (i : Fin 1) → Pattern (d i) := fun _ => .inr ((),())
private def A : RankedExpr 0 (0+1) := .residual 0 (.inr 0)
private def B : RankedExpr 0 (0+1) := .ground (comb 1)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have live : ∀ i, Nonempty (Frontier (p i)) := fun _ => ⟨Sum.inl ()⟩
  have witness : ∃ z : Fin 1 → Source, True ∧ ∀ e ∈ [(A,B)],
      bad.readout () ⟨0,0,1,[(A,B)],(fun _ => True),n,f,d,p⟩ z e.1 ≠
      bad.readout () ⟨0,0,1,[(A,B)],(fun _ => True),n,f,d,p⟩ z e.2 := by
    refine ⟨fun _ => .of true,trivial,?_⟩
    intro e he
    have ep : e = (A,B) := by simpa using he
    subst e
    intro no
    change FreeMagma.of true = FreeMagma.mul (.of true) (.of true) at no
    cases no
  have no := (h 0 0 1 [(A,B)] (fun _ => True) n f d p live).mp witness |>.2.2 (A,B) (by simp)
  exact no rfl

def proof : Registration arena (type_of% (@simultaneous_prefix_separation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@simultaneous_prefix_separation,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,0,1,[],(fun _ => True),n,f,d,p⟩,(fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq
    have no := congrFun eq A
    cases no

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.simultaneous_prefix_separation)
    (Realization signature) (Nat → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.simultaneous_prefix_separation
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.proof
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
    (fun _ p z => fixedEval p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg","arg","body","arg","body","body","fn","arg","fn"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.Shift

abbrev signature : Signature where
  Params := Σ ι : Type, Σ a : Nat, MixedExpr ι
  State p := p.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p x => eval x p.2.2) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => .of true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type} (a : Nat) (x : ι → Source) (E : MixedExpr ι),
    R.readout () ⟨ι,a,shift a E⟩ x =
      substitution^[a] (R.readout () ⟨ι,a,E⟩ x)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have no := @h Unit 1 (fun _ => .of true) (.ground (.of true))
  change FreeMagma.of true = substitution (FreeMagma.of true) at no
  cases no

def proof : Registration arena (type_of% (@eval_shift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eval_shift,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨Unit,0,.residual 0 ()⟩,(fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq
    change FreeMagma.of true = FreeMagma.of false at eq
    cases eq

noncomputable def registration : LeanInformationAudit.Contract.Registration.{1,2,1,0,0,0,1,0,0,0,0,0}
    (@eval_shift) (Realization signature) (Type 1) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.Shift.eval_shift
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.Shift.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => eval x p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","body","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.Shift

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.Bind

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection (MixedExpr eval)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation (bind eval_bind)

abbrev signature : Signature where
  Params := Σ ι : Type, Σ κ : Type, Σ _contexts : ι → MixedExpr κ, ι
  State p := p.2.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => eval z (p.2.2.1 p.2.2.2)) (fun e => nomatch e)

def bad : Realization signature := realize signature (fun _ _ _ => .of false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι κ : Type} (contexts : ι → MixedExpr κ) (z : κ → Source) (E : MixedExpr ι),
    eval z (bind contexts E) = eval (fun i => R.readout () ⟨ι,κ,contexts,i⟩ z) E

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have h := law (fun _ : Unit => (.ground (.of true) : MixedExpr Unit))
    (fun _ => .of true) (.residual 0 ())
  change FreeMagma.of true = FreeMagma.of false at h
  cases h

def proof : Registration arena (type_of% (@eval_bind)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eval_bind,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,bad_law⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨Unit,Unit,(fun _ => .residual 0 ()),()⟩,
      (fun _ => .of true),(fun _ => .of false),?_⟩
    intro h
    change FreeMagma.of true = FreeMagma.of false at h
    cases h

noncomputable def registration : LeanInformationAudit.Contract.Registration.{1,2,1,0,0,0,1,0,0,0,0,0}
    (@eval_bind) (Realization signature) (Type 1) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.Bind.eval_bind
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.Bind.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => eval z (p.2.2.1 p.2.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation
    definition := none
    coordinates := #[0,1,2,5]
    readouts := #[{
      path := #["body","body","body","body","body","arg","fn","arg","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation.Bind
