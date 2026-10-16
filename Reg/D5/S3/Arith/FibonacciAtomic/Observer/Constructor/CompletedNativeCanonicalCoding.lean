import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.CompletedNativeCanonicalCoding
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletedNativeCanonicalCoding
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.CompletedNativeCanonicalCoding
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Code
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ _ X => collapse X) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => primitive 0) (fun e => nomatch e)

/-- Every original scoped variable and every conclusion remains present. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ X, Reduced (collapse X) ∧ expansion (R.readout () () X) = X) ∧
    (∀ C, Reduced C → collapse (expansion C) = C) ∧
    (Function.Injective collapse ∧ (∀ C, Reduced C → ∃ X, collapse X = C)) ∧
    (∀ k C, Reduced C → Reduced (shift k C)) ∧
    (∀ k X, collapse (rho^[k] X) = shift k (collapse X)) ∧
    (∀ C, Reduced C → (expansion C = Omega ↔ C = codeOmega)) ∧
    (∀ n, collapse (atomic n) = primitive n) ∧
    (∀ l r, (¬ ∃ n, node l r = atomic n) →
      collapse (node l r) = fork (collapse l) (collapse r)) ∧
    (∀ l r, fork l r ≠ codeOmega → ¬ (l = codeOmega ∧ r = codeOmega))

def familyRegistration : Registration arena
    ((∀ X, Reduced (collapse X) ∧ expansion (collapse X) = X) ∧
    (∀ C, Reduced C → collapse (expansion C) = C) ∧
    (Function.Injective collapse ∧ (∀ C, Reduced C → ∃ X, collapse X = C)) ∧
    (∀ k C, Reduced C → Reduced (shift k C)) ∧
    (∀ k X, collapse (rho^[k] X) = shift k (collapse X)) ∧
    (∀ C, Reduced C → (expansion C = Omega ↔ C = codeOmega)) ∧
    (∀ n, collapse (atomic n) = primitive n) ∧
    (∀ l r, (¬ ∃ n, node l r = atomic n) →
      collapse (node l r) = fork (collapse l) (collapse r)) ∧
    (∀ l r, fork l r ≠ codeOmega → ¬ (l = codeOmega ∧ r = codeOmega))) := by
  have leaves_differ : leaf true ≠ leaf false := by
    intro h
    have hh := congrArg (fun X => (PFunctor.M.dest X).1) h
    simp only [leaf, PFunctor.M.dest_mk] at hh
    have hb : (true : Bool) = false := Sum.inl.inj hh
    cases hb
  have bad : ¬ arena.Law rejected := by
    intro h
    exact leaves_differ ((h.1 (leaf true)).2.symm.trans (h.1 (leaf false)).2)
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨canonical_coding, rejected, bad⟩
    sensitivity := ⟨?_, fun e => nomatch e⟩
    dependence := ?_
  }
  · intro i
    exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, bad⟩
  · intro i
    refine ⟨(), leaf true, leaf false, ?_⟩
    intro h
    apply leaves_differ
    exact (canonical_coding.1 (leaf true)).2.symm.trans
      ((congrArg expansion h).trans (canonical_coding.1 (leaf false)).2)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    canonical_coding
    (type_of% (realize signature (fun _ _ X => collapse X) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.CompletedNativeCanonicalCoding.canonical_coding
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.CompletedNativeCanonicalCoding.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => collapse X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.CompletedNativeCanonicalCoding
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "arg", "fn", "arg", "arg", "fn"]
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
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.CompletedNativeCanonicalCoding
