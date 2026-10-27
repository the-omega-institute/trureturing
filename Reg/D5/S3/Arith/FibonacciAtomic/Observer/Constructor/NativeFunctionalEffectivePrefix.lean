import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalEffectivePrefix
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalEffectivePrefix
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicFiniteForcing
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (Pattern)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalEffectivePrefix

abbrev signature : Signature where
  Params := Nat
  State _ := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ h := Pattern (h+1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ h X => cutoff (h+1) X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Sum.inl true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ {k m r : Nat} (S : FunctionalSystem k m) (mode : Fin k → Bool)
    (p : Fin k → Nat)
    (R : Fin r → _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.Expr k m)
    (h : Nat) (i : Fin r),
    prefixProgram S mode p R h i = A.readout () h
      (_root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.value
        mode p (canonicalSolution S mode p) (R i))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law (Fin.elim0 : FunctionalSystem 0 0) Fin.elim0 Fin.elim0
    (fun _ : Fin 1 => .ground (.of false)) 0 0
  have good := effective_prefix (Fin.elim0 : FunctionalSystem 0 0) Fin.elim0 Fin.elim0
    (fun _ : Fin 1 => .ground (.of false)) 0 0
  rw [good] at bad
  change (Sum.inl false : Pattern 1) = Sum.inl true at bad
  cases bad

def evidence : Registration arena (type_of% (@effective_prefix)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@effective_prefix, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨0, leaf true, leaf false, ?_⟩
    intro eq
    cases eq

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@effective_prefix) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalEffectivePrefix.effective_prefix.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalEffectivePrefix.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ h X => cutoff (h+1) X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalEffectivePrefix
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalEffectivePrefix
