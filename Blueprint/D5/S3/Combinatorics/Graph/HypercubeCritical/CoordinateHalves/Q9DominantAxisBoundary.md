# A rank obstruction on deleting a coordinate

## Abstract

Paired and empty coordinate fibres in subcubic nine-cube supports

**Theorem 1.1 (The empty-fibre boundary has a nonzero kernel).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary.exists_emptyFibreBoundary_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary.exists_emptyFibreBoundary_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the signed exterior boundary on the retained parity has a nonzero kernel for every real coordinate weighting. Fix a coordinate. Each retained vertex either has its partner along the chosen coordinate in the support or is the sole selected vertex of its fibre. Each opposite-parity exterior vertex belongs either to an empty fibre or to a fibre with a retained singleton.

Put weight one on the chosen coordinate and multiply the other prescribed weights by a real parameter. On an empty-fibre row every entry is divisible by that parameter. Divide these rows by the parameter before taking the determinant of the column Gram matrix. The determinant vanishes for every positive parameter, so the polynomial determinant also vanishes at zero.

At zero, a row with a retained singleton partner isolates its singleton column with coefficient one or minus one. Thus the nonzero kernel survives on paired columns and satisfies all empty-fibre equations.

**Theorem 1.2 (Two actual components satisfy every coordinate test).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary.exists_two_components_with_emptyFibre_kernels`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary.exists_two_components_with_emptyFibre_kernels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each retained parity, choose two distinct actual connected components of an induced subcubic 258-point support before choosing the deleted axis or the transverse weights. Each component has the required signed boundary kernel by its universally singular Huang Gram defect.

The reduced kernel is nonzero for every real transverse weighting, including sparse masks. The rows and columns each record a single fibre, so the condition constrains the projected occupancy when searching for a witness for f₂(Q₉)=3. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary.exists_emptyFibreBoundary_kernel`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary.exists_two_components_with_emptyFibre_kernels`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentSaturation](../ComponentBoundary/Q9ComponentSaturation.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedBoundaryGram](../ComponentBoundary/Q9WeightedBoundaryGram.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedSaturation](../ComponentBoundary/Q9WeightedSaturation.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TranslationAperiodicity](../Translation/Q9TranslationAperiodicity.md)
