# Support and minimum weight of binary cube words

## Abstract

The minimum-support classification and weight divisibility transfer to the Boolean-coordinate cube.

**Definition 1.1 (Support of a binary word).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.binarySites`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.binarySites` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a finite type, the support is the set of sites where the binary word is nonzero.

**Theorem 1.2 (Shared sites cancel in a binary sum).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.add_sites_card_add_twice_inter`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.add_sites_card_add_twice_inter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support of a sum is the symmetric difference of the two supports. Its size plus twice the size of their intersection equals the sum of the two original support sizes.

**Theorem 1.3 (A minimum support in Boolean coordinates is a neighbor shell).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.minimum_kernel_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.minimum_kernel_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In even dimension n at least six, a nonzero binary adjacency-kernel word with support size at most n has support size exactly n, and its support is the set of all single-coordinate flips of a center.

Taking the set of true coordinates turns each Boolean flip into symmetric difference with a singleton. The kernel equation gives even selected neighbor counts. The lower bound in BinaryKernelCrossing forces equality, and BinaryKernelMinimum.minimum_support_iff identifies the support in the coordinate-subset model. Pulling back by the same equivalence gives the Boolean-coordinate shell.

**Theorem 1.4 (Kernel support sizes are divisible by four).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.four_dvd_binarySites_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.four_dvd_binarySites_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a cube of dimension 4m with m positive, every binary adjacency-kernel word has support size divisible by four. The coordinate-subset equivalence preserves binary adjacency and transports the weight congruence from BinaryAdjacencyWeight.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.add_sites_card_add_twice_inter`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.binarySites`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.four_dvd_binarySites_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport.minimum_kernel_support`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight](../../Hypercube/BinaryAdjacencyWeight.md)
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelMinimum](../../Hypercube/BinaryKernelMinimum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel](../ComponentBoundary/BinaryCubeHalfKernel.md)
