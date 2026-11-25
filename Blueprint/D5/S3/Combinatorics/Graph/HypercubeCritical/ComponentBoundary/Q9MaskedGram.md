# Active degrees and the 258-vertex obstruction

## Abstract

Coordinate masks for actual induced components

**Theorem 1.1 (Active degrees bound the rectangular Gram matrix).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.masked_gram_det_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.masked_gram_det_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any row and column vertex sets, give the axes in a mask weight one and the remaining axes weight zero. If the row and column active-degree bounds have product smaller than the number of axes in the mask, subtracting the Gram matrix from the identity scaled by the mask size gives a nonsingular matrix.

The maximum row and column sums of absolute entries bound the infinity operator norms of the signed block and its transpose. Their product bounds the Gram operator norm. A vector in the kernel of the shifted Gram would violate the strict norm bound unless it were zero.

**Theorem 1.2 (An active-degree bound certifies an actual component).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.componentDefect_mask_det_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.componentDefect_mask_det_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any selected set, actual component and retained parity. Count masked neighbors across the two parity sides of that component. If the two uniform degree bounds have product smaller than the mask size, the component defect determinant is nonzero at the mask weights. The component decomposition gives the rectangular block, and the sum of squared mask weights is the mask size.

**Theorem 1.3 (Componentwise determinant certificates exclude size 258).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.card_ne_258_of_component_mask_determinants`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.card_ne_258_of_component_mask_determinants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a parity in any induced subcubic support. If at most one actual component has zero defect determinant at every coordinate mask, the support cannot have size 258. A support of that size would have two distinct components singular at every real coordinate weighting, which includes every mask.

**Theorem 1.4 (Componentwise active-degree certificates exclude size 258).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.card_ne_258_of_component_degree_masks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.card_ne_258_of_component_degree_masks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any induced subcubic support and fixed parity, size 258 is excluded if all but at most one actual component admit their own mask satisfying the active-degree product bound. For example, a component can use five active axes if each vertex has at most two neighbors along those axes.

This condition can be used to exclude proposed supports for Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.card_ne_258_of_component_degree_masks`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.card_ne_258_of_component_mask_determinants`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.componentDefect_mask_det_ne_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram.masked_gram_det_ne_zero`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentSaturation](Q9ComponentSaturation.md)
