/- GID: D5/S3/ConceptDynamics/Faithfulness/CoordinateDeletionRobustness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/CoordinateDeletionRobustness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One more separating coordinate than the deletion budget preserves joint faithfulness. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib

/- Library-search audit trail (2026-08-26):
   * Current-tree searches for coordinate deletion, erasure robustness, separating-coordinate
     cardinality, and restricted joint-readout injectivity found no exact D5 theorem.
   * Exact family hit `JointFaithfulnessLeibnizCriterion.jointReadout` is the canonical
     dependent readout assembled from an indexed observation family and is used directly.
     Body-shape searches for `fun x i => q i x` found that primitive, so no parallel bundle
     is introduced here.
   * Pinned Mathlib contains the exact support lemmas `Finset.card_le_card` and basic filtered
     membership simplification, but no theorem packaging the redundancy/deletion implication.
   * `loogle` and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.CoordinateDeletionRobustness

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- If every distinct state pair is separated by at least `f + 1` coordinates,
then deleting any set of at most `f` coordinates leaves the canonical joint
readout on the surviving coordinates injective. -/
theorem coordinate_deletion_robustness
    {I : Type u} {X : Type v} {O : I -> Type w}
    (q : forall i, X -> O i) (f : Nat)
    (redundant : forall x y, x ≠ y ->
      ∃ separating : Finset I,
        separating.card = f + 1 ∧
          forall i : separating, q i.1 x ≠ q i.1 y) :
    forall deleted : Finset I, deleted.card <= f ->
      Function.Injective
        (jointReadout (fun i : {i // i ∉ deleted} => q i.1)) := by
  classical
  intro deleted hdeleted x y hreadout
  by_contra hxy
  rcases redundant x y hxy with ⟨separating, hcard, hseparates⟩
  have hnotSubset : ¬separating ⊆ deleted := by
    intro hsubset
    have hcardLe := Finset.card_le_card hsubset
    omega
  rw [Finset.not_subset] at hnotSubset
  rcases hnotSubset with ⟨i, hiSeparating, hiDeleted⟩
  have hsame := congrFun hreadout
    (show {i // i ∉ deleted} from ⟨i, hiDeleted⟩)
  exact hseparates ⟨i, hiSeparating⟩ hsame

#print axioms coordinate_deletion_robustness

end D5.S3.ConceptDynamics.Faithfulness.CoordinateDeletionRobustness
