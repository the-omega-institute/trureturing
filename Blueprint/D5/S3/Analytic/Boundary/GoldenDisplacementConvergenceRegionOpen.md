# Golden Displacement Convergence Region Is Open

## Abstract

The golden displacement convergence region is open in its real parameter plane.

**Theorem 1.1 (The golden displacement convergence region is open).**

$$\operatorname{IsOpen}(\{p: \mathbb{R} \times \mathbb{R} \mid \operatorname{Summable}(\operatorname{dTerm}(p.1, p.2))\})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/GoldenDisplacementConvergenceRegionOpen.golden_displacement_convergence_region_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The summability characterization identifies the parameter region with the intersection of two strict affine half-planes.

Each affine expression is continuous on the product parameter space, so the strict inequality defines an open set. Their intersection is therefore open. This records the topological property separately from the already established convexity statement.

Repository searches found no existing IsOpen declaration for this region. Pinned Mathlib supplies isOpen_lt and continuity of the affine maps; the Lean proof combines those facts with the repository's exact two-constraint summability theorem.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/GoldenDisplacementConvergenceRegionOpen.golden_displacement_convergence_region_open`
