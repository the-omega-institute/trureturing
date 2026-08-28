# Golden Displacement Convergence Boundary

## Abstract

The boundary of golden displacement convergence is exactly the graph of its critical-boundary function.

**Theorem 1.1 (The convergence boundary is the critical graph).**

$$\operatorname{frontier}(\left\{p : \mathbb{R} \times \mathbb{R} \mid \operatorname{Summable}(\operatorname{dTerm}(p.1, p.2))\right\}) = \left\{p : \mathbb{R} \times \mathbb{R} \mid \operatorname{goldenDisplacementCriticalBoundary}(p.1) = p.2\right\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/GoldenDisplacementConvergenceBoundary.golden_displacement_convergence_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binding-constraint theorem identifies summability with the strict epigraph of the critical-boundary function. Continuity of the maximum of its two affine branches puts every frontier point on the graph.

The reverse inclusion is substantive. At a graph point (s,w), every positive epsilon gives the convergent point (s,w+epsilon/2) inside the strict epigraph, while the graph point itself lies in its complement. Thus both sides accumulate at the point.

Pinned Mathlib supplies only the applicable frontier-to-equality inclusion. This theorem adds the vertical perturbation required for equality and makes no separate closure or interior claim.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/GoldenDisplacementConvergenceBoundary.golden_displacement_convergence_boundary`
