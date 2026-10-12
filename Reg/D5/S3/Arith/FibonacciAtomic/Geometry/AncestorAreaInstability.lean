import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Combinatorics.Partitions.WordPartitionInverse (wd)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => depth t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 3 ≤ n →
      wd (T n) = wd (U n) ∧ (T n).length = Nat.fib (n+1) ∧
      (U n).length = (T n).length ∧ R.readout () () (T n) = n ∧ depth (U n) = 0 ∧
      ltwo (readout (T n).length (T n)) (readout (T n).length (U n)) = Real.sqrt 2 ∧
      ‖readout (T n).length (T n) - readout (T n).length (U n)‖ = 1 ∧
      ‖normalized (T n).length (T n) - normalized (T n).length (U n)‖ =
        1 / ((Nat.fib (n+1)).choose 2 : ℝ)) ∧
    (¬ ∃ L : ℝ, ∀ s t : Source, s.length = t.length →
      |(depth s : ℝ) - (depth t : ℝ)| ≤ L * ltwo (readout s.length s) (readout s.length t)) ∧
    Filter.Tendsto (fun n : ℕ => 1 / ((Nat.fib (n+1)).choose 2 : ℝ))
      Filter.atTop (nhds 0) ∧
    (∀ (n : ℕ), 3 ≤ n → ∀ ε : ℝ,
      1 / (2 * ((Nat.fib (n+1)).choose 2 : ℝ)) ≤ ε →
      ‖midpoint n - normalized (T n).length (T n)‖ ≤ ε ∧
      ‖midpoint n - normalized (T n).length (U n)‖ ≤ ε ∧
      ∀ E : (Fin ((T n).length-1) → ℝ) → ℝ,
        (n : ℝ)/2 ≤ max |E (midpoint n) - (depth (T n) : ℝ)|
          |E (midpoint n) - (depth (U n) : ℝ)|)

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, by
    intro h
    have he := (h.1 3 (by decide)).2.2.2.1
    change (0 : ℕ) = 3 at he
    norm_num at he⟩
  sensitivity := by
    unfold Sensitivity
    dsimp only [arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, by
        intro h
        have he := (h.1 3 (by decide)).2.2.2.1
        change (0 : ℕ) = 3 at he
        norm_num at he⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    unfold ObservationalDependence
    dsimp only [arena, signature]
    intro i
    refine ⟨(), T 3, U 3, ?_⟩
    have family := result.1 3 (by decide)
    change depth (T 3) ≠ depth (U 3)
    rw [family.2.2.2.1, family.2.2.2.2.1]
    decide

/-- Select the raw native-depth function operand while retaining every clause
of the complete original result as the law. -/
def registration : Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability.result)
    (type_of% (realize signature (fun _ _ t => depth t) (fun e => nomatch e)))
    (Type) (Unit) := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => depth t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "arg", "arg",
        "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability
