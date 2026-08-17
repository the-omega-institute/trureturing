# Paired Top Eigenspace of Path Averaging

## Abstract

Squaring finite zero-boundary path averaging pairs the low and high sine modes and makes their span the full two-dimensional top eigenspace.

For a real vector on Fin N, J averages the left and right neighbours and uses zero beyond the two endpoints. Its sine modes have eigenvalues cos(k pi/(N+1)). Replacing k by N+1-k negates that eigenvalue, so the two edge modes become degenerate after J is squared.

**Theorem 1.1 (Paired sine modes have the same squared eigenvalue).**

$$\operatorname{cos}(theta_{k})^{2} = \operatorname{cos}(theta_{N+1-k})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.paired_mode_cos_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The paired angle is pi minus the original angle. Mathlib's cosine reflection identity changes its sign, and squaring removes that sign. At the spectral edge this pairs mode one with mode N.

**Theorem 1.2 (The edge quadratic value is sharp).**

$$\operatorname{max}_{\lvert c\rvert_{2}=1} Q_{N}(c) = \operatorname{cos}(\frac{\pi}{N+1})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.nearest_neighbor_quadratic_edge_is_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof applies the existing universal quadratic upper bound and the existing normalized sine witness. It packages those two imported facts without re-proving either one.

**Theorem 1.3 (The top-mode space is exactly two-dimensional).**

$$\operatorname{finrank}(\operatorname{span}(\{v_{1}, v_{N}\})) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.top_mode_space_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N at least two, the low and high modes are linearly independent. The first two coordinates separate their coefficients because the high mode alternates the signs of the strictly positive low-mode entries.

**Theorem 1.4 (The full squared top eigenspace is the paired-mode span).**

$$\operatorname{eigenspace}(J^{2}, \operatorname{cos}(\frac{\pi}{N+1})^{2}) = \operatorname{span}(\{v_{1}, v_{N}\})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.squared_top_eigenspace_eq_top_mode_space` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both edge modes have the displayed squared eigenvalue, so their span lies in the squared eigenspace. Conversely, the squared recurrence determines every coordinate from the first two, bounding the full eigenspace dimension by two. Equality of the two subspaces follows.

This theorem characterizes only the finite Dirichlet path operator and its squared spectrum. It introduces no infinite-dimensional or probabilistic spectral claim.

**Theorem 1.5 (The full squared top eigenspace has dimension two).**

$$\operatorname{finrank}(\operatorname{eigenspace}(J^{2}, \operatorname{cos}(\frac{\pi}{N+1})^{2})) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.squared_top_eigenspace_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the paired-span characterization into its independent two-generator dimension theorem gives the exact dimension for every N at least two.

## References

- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.nearest_neighbor_quadratic_edge_is_sharp`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.paired_mode_cos_sq`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.squared_top_eigenspace_eq_top_mode_space`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.squared_top_eigenspace_finrank`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.top_mode_space_finrank`
- Dependency: [D5/S3/QuantumBounds/ReferenceFrameTaxOptimal](../ReferenceFrameTaxOptimal.md)
