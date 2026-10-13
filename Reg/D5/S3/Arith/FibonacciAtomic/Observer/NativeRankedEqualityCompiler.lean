import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection (MixedExpr)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler

abbrev signature : Signature where
  Params := Σ k : Nat, Σ _m : Nat, Fin k → Nat
  State p := Fin p.2.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := RankedExpr p.1 p.2.1 → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => rankedEval p.2.2 z) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => .of true) (fun e => nomatch e)

abbrev equalityArena : Arena where
  signature := signature
  Law R := ∀ (k m : Nat) (z : Fin m → Source) (E F : RankedExpr k m),
    (equalityFormula z E F).IsQF ∧ ∀ n : Fin k → Nat,
      (equalityFormula z E F).Realize n ↔
        R.readout () ⟨k,m,n⟩ z E = R.readout () ⟨k,m,n⟩ z F

private theorem bad_equality_law : ¬ equalityArena.Law bad := by
  intro law
  let z : Fin 0 → Source := fun i => nomatch i
  let n : Fin 0 → Nat := fun i => nomatch i
  have h := ((law 0 0 z (.ground (.of true)) (.ground (.of false))).2 n).mpr rfl
  have eq := ((ranked_equality_compilation 0 0 z
    (.ground (.of true)) (.ground (.of false))).2 n).mp h
  change FreeMagma.of true = FreeMagma.of false at eq
  cases eq

def equalityProof : Registration equalityArena (type_of% (@ranked_equality_compilation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ranked_equality_compilation, bad, bad_equality_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, bad_equality_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,1,(fun j => nomatch j)⟩,
      (fun _ => .of true), (fun _ => .of false), ?_⟩
    intro h
    have he := congrFun h (.residual 0 (.inr 0))
    change FreeMagma.of true = FreeMagma.of false at he
    cases he

abbrev supportArena : Arena where
  signature := signature
  Law R := ∀ (k m : Nat) (pairs : List (RankedExpr k m × RankedExpr k m)),
    (supportFormula pairs).IsQF ∧ ∀ n : Fin k → Nat,
      (supportFormula pairs).Realize n ↔ ∃ z : Fin m → Source,
        ∀ p ∈ pairs, R.readout () ⟨k,m,n⟩ z p.1 ≠ R.readout () ⟨k,m,n⟩ z p.2

private theorem bad_support_law : ¬ supportArena.Law bad := by
  intro law
  let z : Fin 0 → Source := fun i => nomatch i
  let n : Fin 0 → Nat := fun i => nomatch i
  let pairs : List (RankedExpr 0 0 × RankedExpr 0 0) :=
    [(.ground (.of true), .ground (.of false))]
  have hs : (supportFormula pairs).Realize n :=
    ((support_compilation 0 0 pairs).2 n).mpr ⟨z, by
      intro p hp
      obtain rfl := List.mem_singleton.mp hp
      intro h
      change FreeMagma.of true = FreeMagma.of false at h
      cases h⟩
  obtain ⟨v,hv⟩ := ((law 0 0 pairs).2 n).mp hs
  exact (hv _ (List.mem_singleton_self _)) rfl

def supportProof : Registration supportArena (type_of% (@support_compilation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨support_compilation, bad, bad_support_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, bad_support_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,1,(fun j => nomatch j)⟩,
      (fun _ => .of true), (fun _ => .of false), ?_⟩
    intro h
    have he := congrFun h (.residual 0 (.inr 0))
    change FreeMagma.of true = FreeMagma.of false at he
    cases he

noncomputable def equalityRegistration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler.ranked_equality_compilation)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler.ranked_equality_compilation
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler.equalityProof
  realizationSource := none
  generated := false
  arena := .source ⟨equalityArena⟩
  objectArena := .source ⟨equalityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source equalityArena ⟨equalityProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => rankedEval p.2.2 z)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler
    definition := none
    coordinates := #[0,1,5]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","arg","fn","arg","fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def supportRegistration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler.support_compilation)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler.support_compilation
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler.supportProof
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => rankedEval p.2.2 z)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","arg","body","arg","arg","body","body","body","fn","arg","fn"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms equalityProof
#print axioms supportProof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler
