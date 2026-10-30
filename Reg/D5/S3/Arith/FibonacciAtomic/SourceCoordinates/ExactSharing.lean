import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.ExactSharing
import Reg.Support.DependentFamily

/-! The complete source theorem is reconstructed from its rooted-fringe cardinality readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.ExactSharing

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source composition)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability (T)
open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.ExactSharing
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => (fringes (T n)).card) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ,
      composition (T n) = GraftAffineClosure.atomicBlock n ∧
      (T n).length = Nat.fib (n + 1) ∧
      expandedNodes (T n) = 2 * Nat.fib (n + 1) - 1 ∧
      (n < 2 → fringes (T n) = {T n} ∧ (fringes (T n)).card = 1) ∧
      (2 ≤ n → fringes (T n) = (Finset.range (n + 1)).image T ∧
        R.readout () () n = n + 1)) ∧
    (∀ (A : Type u) (μ : A → A → A) (E : Source → A),
      (∀ s t, E (.mul s t) = μ (E s) (E t)) → ∀ n : ℕ,
        sharedEval μ (E (.of true)) (E (.of false)) n = (E (T n), n - 1))

theorem erased_fails : ¬ arena.{u}.Law erased := by
  intro h
  have htwo := ((h.1 2).2.2.2.2 (by decide)).2
  change (0 : ℕ) = 3 at htwo
  omega

def family : Registration arena.{u} (type_of% (@exact_sharing.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_sharing, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change (fringes (T 0)).card ≠ (fringes (T 2)).card
    have hzero := ((exact_sharing.{u}.1 0).2.2.2.1 (by decide)).2
    have htwo := ((exact_sharing.{u}.1 2).2.2.2.2 (by decide)).2
    rw [hzero, htwo]
    decide

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exact_sharing.{u})
    (type_of% (realize signature (fun _ _ n => (fringes (T n)).card) (fun e => nomatch e)))
    Unit Unit where
  unitName := (`D5.S3.Arith.FibonacciAtomic.SourceCoordinates.ExactSharing.exact_sharing).str
    "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.ExactSharing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (fringes (T n)).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.ExactSharing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "arg", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.ExactSharing
