import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Windows.OddBlockGcdPeriodicity

/-! The square-window gcd is observed on its full integer-seed and natural-length domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Windows.OddBlockGcdPeriodicity

open _root_.D5.S3.Arith.FibonacciAtomic.Windows.OddBlockGcdPeriodicity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _a : ℤ, ℤ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p k => squareGcd p.1 p.2 k) (fun e => nomatch e)

/-- Only the square-gcd observation in its universal divisor specification varies.
All other clauses of the complete original statement remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ a b : ℤ,
    (g a b 0 = a ∧ g a b 1 = b ∧
      ∀ n : ℕ, g a b (n + 2) = g a b n + g a b (n + 1)) ∧
    (∀ u : ℕ → ℤ, u 0 = a → u 1 = b →
      (∀ n, u (n + 2) = u n + u (n + 1)) → ∀ n, u n = g a b n) ∧
    (∀ (k : ℕ) (d : ℤ),
      (d ∣ (sumGcd a b k : ℤ) ↔ ∀ t : ℕ, d ∣ sumWindow a b t k) ∧
      (d ∣ (R.readout () ⟨a, b⟩ k : ℤ) ↔ ∀ t : ℕ, d ∣ squareWindow a b t k)) ∧
    (∀ (c : ℤ) (k : ℕ),
      sumGcd (c * a) (c * b) k = c.natAbs * sumGcd a b k ∧
      squareGcd (c * a) (c * b) k = c.natAbs ^ 2 * squareGcd a b k) ∧
    (∃ P : ℕ, 0 < P ∧ ∀ j : ℕ,
      sumGcd a b (2 * (j + P) + 1) = sumGcd a b (2 * j + 1) ∧
      squareGcd a b (2 * (j + P) + 1) = squareGcd a b (2 * j + 1)) ∧
    ((a = 0 ∧ b = 0) → ∀ k : ℕ, sumGcd a b k = 0 ∧ squareGcd a b k = 0)

abbrev sourceScope := type_of% (@result)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hs := ((h 0 1).2.2.1 1 0).2.mp (by
    change (0 : ℤ) ∣ (0 : ℤ)
    exact dvd_rfl)
  have hb := hs 0
  norm_num [squareWindow, g, _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.step] at hb

theorem observational_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 1⟩, 1, 3, ?_⟩
  change squareGcd 0 1 1 ≠ squareGcd 0 1 3
  norm_num [squareGcd, squareWindow, g,
    _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.step, Finset.sum_range_succ,
    Function.iterate_succ_apply']

def family : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp result, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := observational_dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Windows.OddBlockGcdPeriodicity.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Windows.OddBlockGcdPeriodicity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => squareGcd p.1 p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Windows.OddBlockGcdPeriodicity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "body", "body",
        "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

example : Nonempty signature.Params := ⟨⟨-1, 3⟩⟩

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.Windows.OddBlockGcdPeriodicity
