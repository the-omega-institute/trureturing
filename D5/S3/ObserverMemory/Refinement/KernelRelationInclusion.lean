/- GID: D5/S3/ObserverMemory/Refinement/KernelRelationInclusion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/KernelRelationInclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refinement factorization makes the fine equality kernel contained in the coarse one. -/

import D5.S0.Rewriting.Quotients.RelativeIdentityRefinement
import D5.S3.ObserverMemory.Refinement.FactorizationCategory

/- Library-search audit trail (2026-08-25):
   * Exact family hit: `FactorizationCategory.Refines` is the canonical
     factorization-data refinement structure and is imported directly.
   * Exact repository hit: `relative_identity_refinement` proves the required
     kernel inclusion as its first public conjunct and is applied directly.
   * Pinned Mathlib hit: `Function.FactorsThrough` is the same pointwise
     fiber-constancy predicate, but no theorem there consumes the repository's
     canonical refinement structure. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Refinement.KernelRelationInclusion

open D5.S0.Rewriting.Quotients.RelativeIdentityRefinement
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ObserverMemory.Refinement.FactorizationCategory

/-- Equality under a finer readout implies equality under every readout obtained
from it by the canonical refinement factorization. -/
theorem refinement_implies_kernel_inclusion
    {X Fine Coarse : Type*}
    (fine : Concept X Fine) (coarse : Concept X Coarse)
    (refinement : Refines fine coarse) :
    forall {x y : X}, fine x = fine y -> coarse x = coarse y := by
  have kernelInclusion : Setoid.ker fine <= Setoid.ker coarse :=
    (relative_identity_refinement fine coarse refinement.factor
      (funext refinement.commutes)).1
  exact kernelInclusion

#print axioms refinement_implies_kernel_inclusion

end D5.S3.ObserverMemory.Refinement.KernelRelationInclusion
