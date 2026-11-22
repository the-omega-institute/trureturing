# Physical BKM defects under classical flag refinement

## Abstract

Positive normalized refinements of classical flags preserve the actual marginal and physical BKM defects.

**Definition 1.1 (Refined reference).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinement.refinedBlocks`

*Formalization.* `D5/S3/Quantum/Recovery/BKMFlagRefinement.refinedBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use a finite child set for each parent flag. Its child blocks are the parent block multiplied by the corresponding weights. The joint reference acts on retained space tensored with the flag space.

**Theorem 1.2 (Preservation of the actual marginal).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinement.marginal_refined`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinement.marginal_refined` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the right partial trace gives the sum of the blocks. When each parent's weights sum to one, summing its child blocks recovers the parent, so the old and new right partial traces agree.

**Definition 1.3 (Logarithmic commutator defect).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinement.logDefect`

*Formalization.* `D5/S3/Quantum/Recovery/BKMFlagRefinement.logDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the identity lift of the marginal logarithm from the joint logarithm, then commute with the identity lift of the retained observable. The defect is the real trace of the joint reference times the squared absolute value of that commutator.

**Definition 1.4 (BKM metric gap).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinement.bkmGap`

*Formalization.* `D5/S3/Quantum/Recovery/BKMFlagRefinement.bkmGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the joint BKM quadratic form of the lifted observable from the marginal BKM quadratic form of the retained observable. Both forms use the integral of the left and right matrix powers with exponents adding to one.

**Theorem 1.5 (Exact invariance of both defects).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinement.refine_defects`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinement.refine_defects` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive definite block family, every positive normalized refinement and every retained matrix, the logarithmic defect and BKM gap agree before and after refinement. A positive scalar adds a scalar identity to a block logarithm, so the commutator is unchanged. The block trace term scales by the child weight. In the BKM integral the two powers contribute scalar factors whose exponents sum to one. Summing the child contributions thus restores both original block sums.

**Theorem 1.6 (Faithful normalization and physical defects).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinement.physical_refinement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinement.physical_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a nonempty parent flag set, positive definite parent blocks whose joint trace is one, positive weights summing to one at each parent and a Hermitian retained observable. Both joint references are positive definite and the refined joint trace is one. The original marginal is positive definite with trace one and equals the refined marginal. Both identity lifts are Hermitian and the physical defects agree.

**Theorem 1.7 (Positive gap and defect ratio).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinement.refine_positive_gap_and_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinement.refine_positive_gap_and_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the original BKM gap is strictly positive, the refined gap is strictly positive and the ratio of the logarithmic defect to the BKM gap is equal before and after refinement.

**Theorem 1.8 (Uniform splitting of one flag).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinement.uniform_refinement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinement.uniform_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split a chosen parent into a positive number of equal-weight children and give each other parent one child of weight one. The actual marginal and both defects are preserved.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinement.bkmGap`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinement.logDefect`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinement.marginal_refined`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinement.physical_refinement`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinement.refine_defects`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinement.refine_positive_gap_and_ratio`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinement.refinedBlocks`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinement.uniform_refinement`
- Dependency: [D5/S3/Quantum/FixedAlgebra/RecordFixedAlgebraDecomposition](../FixedAlgebra/RecordFixedAlgebraDecomposition.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMDiagonalStability](BKMDiagonalStability.md)
