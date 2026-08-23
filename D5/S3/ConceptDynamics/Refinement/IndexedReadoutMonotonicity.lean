/- GID: D5/S3/ConceptDynamics/Refinement/IndexedReadoutMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/IndexedReadoutMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Larger finite index sets refine joint readouts and shrink equality kernels. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-24):
   * Exact current-tree hits `ConceptJoinUniversal.Refines` and
     `JointFaithfulnessLeibnizCriterion.jointReadout` are the source's
     factorization relation and dependent product readout; both are imported.
   * Repository searches for indexed joint-readout monotonicity and restriction
     along a finite-set inclusion found no theorem supplying both public clauses.
     The adjacent `JointPredictionRelation.jointObservation` belongs to a separate
     family and is not redeclared here.
   * Pinned Mathlib searches for a `Setoid.ker` composition-inclusion theorem found
     no applicable exact hit. The kernel clause follows directly by evaluating
     equality of the fine dependent readout at each coarse coordinate.
   * `loogle` and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.IndexedReadoutMonotonicity

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- Restricting a dependent joint readout from a larger finite index set to a
smaller one witnesses readout refinement and reverse inclusion of equality kernels. -/
theorem indexed_readout_monotonicity
    {I : Type u} {X : Type v} {O : I -> Type w}
    (q : forall i, X -> O i) {J K : Finset I} (hJK : J ⊆ K) :
    Refines
        (jointReadout (fun j : J => q j.1))
        (jointReadout (fun k : K => q k.1)) ∧
      Setoid.ker (jointReadout (fun k : K => q k.1)) <=
        Setoid.ker (jointReadout (fun j : J => q j.1)) := by
  let restrict : (forall k : K, O k.1) -> (forall j : J, O j.1) :=
    fun values j => values ⟨j.1, hJK j.2⟩
  constructor
  · refine ⟨restrict, ?_⟩
    funext x j
    rfl
  · intro x y hxy
    change (fun j : J => q j.1 x) = fun j : J => q j.1 y
    funext j
    exact congrFun hxy ⟨j.1, hJK j.2⟩

#print axioms indexed_readout_monotonicity

end D5.S3.ConceptDynamics.Refinement.IndexedReadoutMonotonicity
