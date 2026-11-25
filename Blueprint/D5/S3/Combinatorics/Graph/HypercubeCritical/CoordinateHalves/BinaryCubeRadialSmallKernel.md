# Small radial binary kernel words on the eight-cube

## Abstract

The no-split star hypothesis reduces a small kernel word to one eight-point Hamming layer.

**Definition 1.1 (Set of true coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.trueCoords`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.trueCoords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Select the coordinate indices at which the vertex has bit true.

**Definition 1.2 (Hamming weight of a cube vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.hammingWeight`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.hammingWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count the true coordinates, equivalently the Hamming distance from the all-false vertex.

**Definition 1.3 (Weight of a binary cube word).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.supportWeight`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.supportWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count the vertices where the word is nonzero.

**Definition 1.4 (Equivalence with subsets of coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.trueCoordsEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.trueCoordsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the set of true coordinates. The inverse sends a set of indices to the vertex whose bits are their membership indicators. This identifies a Hamming layer with the sets of the corresponding size.

**Theorem 1.5 (A radial kernel profile is constant on the even layers).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.radial_kernel_even_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.radial_kernel_even_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be the layer profile of a binary kernel word on Q8. At a vertex of radius k, the adjacency sum receives k terms from radius k − 1 and 8 − k terms from radius k + 1. At k equal to 1, 3, 5 or 7, both multiplicities are odd, so the two neighboring profile values coincide. This gives equality of the values at radii 0, 2, 4, 6 and 8.

**Theorem 1.6 (A nonzero small radial kernel word occupies one shell).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.radial_small_kernel_one_shell`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.radial_small_kernel_one_shell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a Q8 binary kernel word is constant on each Hamming layer and has positive weight at most twelve. Layers 2, 3 and 5 each exceed the weight budget. The even-layer equations then force every even layer to vanish. The two remaining layers have radii 1 and 7 and size eight each, so exactly one is occupied and the word has weight eight.

**Theorem 1.7 (A small kernel word with no split on the star is a translated shell).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.no_split_small_kernel_one_shell`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.no_split_small_kernel_one_shell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a coordinate r of Q8. For each j distinct from r, assume the double flip preserves the word on all unequal-bit vertices or on all equal-bit vertices for r and j. If the word lies in the kernel and has positive weight at most twelve, there is a translation with r bit false whose pullback has support exactly the radius-one or radius-seven layer. The original word has weight eight.

The star swaps give constancy by Hamming layer after translation. Translation commutes with each coordinate flip and is a bijection, so it preserves the kernel equation and support size. The radius-seven layer is the open neighbor shell of the antipode of the all-false vertex.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.hammingWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.no_split_small_kernel_one_shell`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.radial_kernel_even_profile`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.radial_small_kernel_one_shell`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.supportWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.trueCoords`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel.trueCoordsEquiv`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel](../ComponentBoundary/BinaryCubeHalfKernel.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation](BinaryCubeSwapConjugation.md)
