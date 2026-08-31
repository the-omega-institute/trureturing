# Golden Inverse-Branch Fixed Point

## Abstract

The first inverse branch has the inverse golden ratio as its unique positive fixed point.

**Theorem 1.1 (The positive fixed point is characterized exactly).**

$$\forall x \in \mathbb{R}, 0 < x \Rightarrow (\frac{1}{x + 1} = x \iff x = \varphi^{-1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenInverseBranchFixedPoint.golden_inverse_branch_positive_fixed_point_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real x, the equation one over x plus one equals x holds exactly when x is the inverse golden ratio.

The forward direction clears the positive denominator and compares the resulting quadratic with the golden-ratio quadratic. The reverse direction applies the reciprocal identity from the frozen transfer triangle.

Repository and pinned Mathlib searches found the supporting golden-ratio identities but no public theorem stating this fixed-point characterization.

## References

- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenInverseBranchFixedPoint.golden_inverse_branch_positive_fixed_point_iff`
- Dependency: [D5/S3/Analytic/Characterizations/GoldenTransferTriangle](GoldenTransferTriangle.md)
