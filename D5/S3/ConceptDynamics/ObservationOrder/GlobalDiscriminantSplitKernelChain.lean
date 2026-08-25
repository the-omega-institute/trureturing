/- GID: D5/S3/ConceptDynamics/ObservationOrder/GlobalDiscriminantSplitKernelChain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/GlobalDiscriminantSplitKernelChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Global equivalence refines discriminant equivalence, which refines split equivalence. -/

import D5.S0.Rewriting.Quotients.RelativeIdentityRefinement
import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-25):
   * Repository searches for global, discriminant, and split readout kernels
     found no theorem stating this two-stage inclusion chain.
   * Exact family hits `Concept` and `Refines` supply the canonical readout
     carrier and factorization predicate; both are imported rather than forked.
   * Exact repository hit `relative_identity_refinement` proves the kernel
     inclusion induced by one factorization and is applied to both stages.
   * Pinned Mathlib hits `Function.FactorsThrough`, `factorsThrough_iff`,
     `FactorsThrough.comp_left`, and `FactorsThrough.comp_right` are adjacent,
     but none packages the two public relation inclusions below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationOrder.GlobalDiscriminantSplitKernelChain

open D5.S0.Rewriting.Quotients.RelativeIdentityRefinement
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- If the discriminant readout factors through the global classifier and the
split readout factors through the discriminant, global equality implies
discriminant equality, which in turn implies split equality. -/
theorem global_discriminant_split_kernel_chain
    {X GlobalValue DiscriminantValue SplitValue : Type*}
    (global : Concept X GlobalValue)
    (discriminant : Concept X DiscriminantValue)
    (split : Concept X SplitValue)
    (globalPreservesDiscriminant : Refines discriminant global)
    (splitDependsOnDiscriminant : Refines split discriminant) :
    (Setoid.ker global <= Setoid.ker discriminant) ∧
      (Setoid.ker discriminant <= Setoid.ker split) := by
  rcases globalPreservesDiscriminant with ⟨forgetDiscriminant, hDiscriminant⟩
  rcases splitDependsOnDiscriminant with ⟨readSplit, hSplit⟩
  exact
    ⟨(relative_identity_refinement global discriminant forgetDiscriminant
        hDiscriminant).1,
      (relative_identity_refinement discriminant split readSplit hSplit).1⟩

#print axioms global_discriminant_split_kernel_chain

end D5.S3.ConceptDynamics.ObservationOrder.GlobalDiscriminantSplitKernelChain
