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
  Params := ℕ
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := Fin (m-1) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m t => readout m t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 3 ≤ n →
      wd (T n) = wd (U n) ∧ (T n).length = Nat.fib (n+1) ∧
      (U n).length = (T n).length ∧ depth (T n) = n ∧ depth (U n) = 0 ∧
      ltwo (R.readout () (T n).length (T n)) (R.readout () (T n).length (U n)) = Real.sqrt 2 ∧
      ‖R.readout () (T n).length (T n) - R.readout () (T n).length (U n)‖ = 1 ∧
      ‖normalized (T n).length (T n) - normalized (T n).length (U n)‖ =
        1 / ((Nat.fib (n+1)).choose 2 : ℝ)) ∧
    (¬ ∃ L : ℝ, ∀ s t : Source, s.length = t.length →
      |(depth s : ℝ) - (depth t : ℝ)| ≤ L * ltwo (R.readout () s.length s) (R.readout () s.length t)) ∧
    Filter.Tendsto (fun n : ℕ => 1 / ((Nat.fib (n+1)).choose 2 : ℝ))
      Filter.atTop (nhds 0) ∧
    (∀ (n : ℕ), 3 ≤ n → ∀ ε : ℝ,
      1 / (2 * ((Nat.fib (n+1)).choose 2 : ℝ)) ≤ ε →
      ‖midpoint n - normalized (T n).length (T n)‖ ≤ ε ∧
      ‖midpoint n - normalized (T n).length (U n)‖ ≤ ε ∧
      ∀ E : (Fin ((T n).length-1) → ℝ) → ℝ,
        (n : ℝ)/2 ≤ max |E (midpoint n) - (depth (T n) : ℝ)|
          |E (midpoint n) - (depth (U n) : ℝ)|)

def evidence : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, by
    intro h
    have he := (h.1 3 (by decide)).2.2.2.2.2.2.1
    change ‖(0 : Fin ((T 3).length-1) → ℝ) - 0‖ = 1 at he
    norm_num at he⟩
  sensitivity := by
    unfold Sensitivity
    dsimp only [arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, by
        intro h
        have he := (h.1 3 (by decide)).2.2.2.2.2.2.1
        change ‖(0 : Fin ((T 3).length-1) → ℝ) - 0‖ = 1 at he
        norm_num at he⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    unfold ObservationalDependence
    dsimp only [arena, signature]
    intro i
    refine ⟨3, T 3, U 3, ?_⟩
    intro h
    have he := congrFun h (0 : Fin (3-1))
    norm_num [actual, realize, readout, T, U, rotated,
      _root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval.coordinates,
      _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.substitution,
      Function.iterate_succ_apply'] at he

/-- The source coordinate selection remains unspecified until its complete
raw reconstruction is supported for every clause of the original statement. -/
def registration : Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability.result)
    (type_of% (realize signature (fun _ m t => readout m t) (fun e => nomatch e)))
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
  readout := some (realize signature (fun _ m t => readout m t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Source
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability
