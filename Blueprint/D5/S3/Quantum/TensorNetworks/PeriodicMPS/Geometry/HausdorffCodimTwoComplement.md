# Path-connected complements of sets of small Hausdorff dimension

## Abstract

Path-connected complements of sets of small Hausdorff dimension

**Theorem 1.1 (Path-connected complements of sets of small Hausdorff dimension).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Geometry/HausdorffCodimTwoComplement.isPathConnected_diff_of_dimH_add_one_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Geometry/HausdorffCodimTwoComplement.isPathConnected_diff_of_dimH_add_one_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be open and connected in a finite-dimensional real normed space of dimension d. If the Hausdorff dimension of B plus one is strictly less than d, then U minus B is path connected and dense in U.

Inside a convex neighborhood, project the excluded set from each endpoint onto a common transverse slice. Each projected set has Hausdorff dimension below that of the slice. Choosing a point outside both projected sets yields two line segments in the complement. Relative density and the connectedness of U extend this local construction to paths across U.

For a closed B of Hausdorff dimension at most d minus two with d at least two, the complement is also open.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Geometry/HausdorffCodimTwoComplement.isPathConnected_diff_of_dimH_add_one_lt`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRegularComplement](../PeriodicMPSRegularComplement.md)
