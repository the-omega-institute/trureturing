/- GID: D5/S3/ConceptDynamics/Termination/FiniteDefectTermination
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Termination/FiniteDefectTermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict defect removal on a finite carrier stops within the initial defect count. -/

import Mathlib.Data.Set.Card
import Mathlib.Tactic

/- Library-search audit trail (2026-08-23):
   * Repository searches for finite defect termination and strict set descent
     found the related partition theorem `finite_strict_repairs_stabilize`, but
     no accepted declaration with the source's sequence of defect sets.
   * Exact pinned-Mathlib hits `Set.ncard_lt_ncard` and `Set.ncard_eq_zero`
     respectively turn strict inclusion into cardinal descent and zero finite
     cardinality into emptiness; both are applied directly below.
   * `loogle` and `leansearch` were unavailable on PATH; no exact packaged
     bounded-termination theorem was found in the pinned library. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Termination.FiniteDefectTermination

/-- If every nonterminal repair changes the defect set and no repair adds a
defect, some defect set is empty by the initial defect-set cardinality. -/
theorem finite_defect_repairs_terminate
    {W : Type*} [Finite W]
    (defects : Nat -> Set W)
    (strictChange : forall n,
      defects n ≠ ∅ -> defects (n + 1) ≠ defects n)
    (noNewDefects : forall n, defects (n + 1) ⊆ defects n) :
    exists n, n ≤ (defects 0).ncard ∧ defects n = ∅ := by
  classical
  let initialCount := (defects 0).ncard
  by_contra noStoppingIndex
  have nonemptyThrough : forall n, n ≤ initialCount -> defects n ≠ ∅ := by
    intro n hn emptyAtN
    exact noStoppingIndex ⟨n, hn, emptyAtN⟩
  have cardinalDrops : forall n, n < initialCount ->
      (defects (n + 1)).ncard < (defects n).ncard := by
    intro n hn
    exact Set.ncard_lt_ncard
      ((noNewDefects n).ssubset_of_ne
        (strictChange n (nonemptyThrough n hn.le)))
      (Set.toFinite _)
  have countBound : forall n, n ≤ initialCount ->
      (defects n).ncard + n ≤ initialCount := by
    intro n hn
    induction n with
    | zero =>
        simp [initialCount]
    | succ n inductionHypothesis =>
        have previousWithin : n ≤ initialCount := Nat.le_trans (Nat.le_succ n) hn
        have previousBound := inductionHypothesis previousWithin
        have drop := cardinalDrops n (Nat.lt_of_succ_le hn)
        omega
  have finalCardinalityZero : (defects initialCount).ncard = 0 := by
    have := countBound initialCount le_rfl
    omega
  have finalDefectsEmpty : defects initialCount = ∅ :=
    (Set.ncard_eq_zero (s := defects initialCount) (Set.toFinite _)).mp
      finalCardinalityZero
  exact nonemptyThrough initialCount le_rfl finalDefectsEmpty

#print axioms finite_defect_repairs_terminate

end D5.S3.ConceptDynamics.Termination.FiniteDefectTermination
