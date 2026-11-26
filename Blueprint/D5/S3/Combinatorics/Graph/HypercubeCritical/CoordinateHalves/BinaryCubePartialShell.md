# Binary adjacency of a partial neighbor shell

## Abstract

The adjacency image of a partial shell counts the pairs of selected and omitted directions and the center parity.

**Definition 1.1 (Indicator of a partial shell).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell.shellWord`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell.shellWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word is one at the neighbors reached from the center in a selected direction and zero at every other vertex.

**Theorem 1.2 (The image away from the center counts selected–omitted pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell.partial_shell_outside_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell.partial_shell_outside_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension n choose s coordinate directions at a center and take the binary indicator of those s neighbors. Away from the center, the adjacency image is supported precisely on double flips in one selected and one omitted direction. Each such pair gives a distinct site, so the support away from the center has size s(n − s).

**Theorem 1.3 (Exact image weight of a partial shell).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell.partial_shell_image_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell.partial_shell_image_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full image has weight s(n − s) plus the residue of s modulo two. The coefficient at the center is the sum of the s selected neighbors in the binary field.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell.partial_shell_image_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell.partial_shell_outside_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell.shellWord`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport](BinaryCubeKernelSupport.md)
