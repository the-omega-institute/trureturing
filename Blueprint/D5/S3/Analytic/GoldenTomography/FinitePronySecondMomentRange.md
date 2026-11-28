# Attainable second moments of positive Prony families

## Abstract

Which second moments can agree with the same mass and mean?

**Theorem 1.1 (The second-moment interval and the minimum pole count).**

Lean statement: `D5/S3/Analytic/GoldenTomography/FinitePronySecondMomentRange.finite_prony_second_moment_range`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronySecondMomentRange.finite_prony_second_moment_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Work over a linearly ordered field. Fix a positive mass M and a mean x strictly between a and b. Consider finite families of distinct nodes in the open interval with strictly positive weights and moments of orders zero and one equal to M and M times x. Their second moments range from M times x squared, inclusive, to M times the quantity (a + b) x minus a b, exclusive. A realizing family has one node if and only if its second moment equals the lower endpoint. Each interior second moment admits a two-node family. The minimum number of nodes realizing the full moment triple is one at the lower endpoint and two in the interior.

The weighted sum of squared distances from the mean gives the lower slack. If it vanishes, positivity forces every node to equal the mean. The upper slack is the weighted sum of the products of the two distances from each node to the interval endpoints. Every summand is positive, and the positive mass implies there is at least one node.

For positive variance v, choose the left distance d halfway between v/(b − x) and x − a. The right distance e is v divided by d. Weights proportional to e and d center the two nodes at x and give variance d times e. Both nodes lie strictly inside the interval. The upper variance bound is the strict form of Bhatia and Davis, A Better Bound on the Variance (doi:10.1080/00029890.2000.12005203).

## References

- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronySecondMomentRange.finite_prony_second_moment_range`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction](FinitePronyHankelReconstruction.md)
