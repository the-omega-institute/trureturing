/- GID: D5/S3/ConceptDynamics/Refinement/LeastCommonReadoutRefinement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/LeastCommonReadoutRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical joint readout is the least common refinement. -/

import D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

/- Library-search audit trail (2026-08-24):
   * Exact repository hit
     `ConceptJoinUniversal.concept_join_universal` constructs the canonical
     product readout and supplies both projections and its universal
     least-common-refinement factorization. It is applied directly below.
   * Exact repository hit
     `ConceptKernelOrderDuality.concept_kernel_order_duality` supplies the
     kernel-intersection equation for that same canonical readout and is applied
     directly below.
   * `ObserverMemory.Fusion.LeastCommonRefinement` is the source-named adjacent
     quotient construction. Its quotient uses the same intersection relation,
     exposed by the final public conjunct, but its theorem assumes an arbitrary
     surjective quotient presentation rather than raw concept readouts.
   * Repository and pinned-Mathlib searches found no distinct readout primitive
     or stronger bridge requiring reconciliation. `loogle` and `leansearch`
     executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.LeastCommonReadoutRefinement

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

universe u

/-- The canonical joint readout refines both components, is below every common
refinement, and realizes the intersection of their indistinguishability kernels. -/
theorem least_common_readout_refinement
    {X C D : Type u} (q_J : Concept X C) (q_K : Concept X D) :
    Refines q_J (conceptJoin q_J q_K) ∧
      Refines q_K (conceptJoin q_J q_K) ∧
      (∀ {E : Type u} (q_E : Concept X E),
        Refines q_J q_E → Refines q_K q_E →
          Refines (conceptJoin q_J q_K) q_E) ∧
      Setoid.ker (conceptJoin q_J q_K) =
        Setoid.ker q_J ⊓ Setoid.ker q_K := by
  refine ⟨
    (concept_join_universal q_J q_K (conceptJoin q_J q_K)).1,
    (concept_join_universal q_J q_K (conceptJoin q_J q_K)).2.1,
    ?_,
    (concept_kernel_order_duality X).2.2.1 q_J q_K⟩
  intro E q_E hJ hK
  exact (concept_join_universal q_J q_K q_E).2.2 hJ hK

example :
    Refines (id : Bool → Bool)
        (conceptJoin (id : Bool → Bool) (fun _ => ())) ∧
      Refines (fun _ : Bool => ())
        (conceptJoin (id : Bool → Bool) (fun _ => ())) ∧
      (∀ {E : Type} (q_E : Concept Bool E),
        Refines (id : Bool → Bool) q_E →
          Refines (fun _ : Bool => ()) q_E →
          Refines (conceptJoin (id : Bool → Bool) (fun _ => ())) q_E) ∧
      Setoid.ker (conceptJoin (id : Bool → Bool) (fun _ => ())) =
        Setoid.ker (id : Bool → Bool) ⊓ Setoid.ker (fun _ : Bool => ()) := by
  exact least_common_readout_refinement
    (id : Bool → Bool) (fun _ : Bool => ())

#print axioms least_common_readout_refinement

end D5.S3.ConceptDynamics.Refinement.LeastCommonReadoutRefinement
