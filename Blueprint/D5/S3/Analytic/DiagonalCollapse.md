# Diagonal Collapse of the Two-Face Generating Function

## Abstract

The two-face generating function collapses on the diagonal to a geometric series.

**Theorem 1.1 (The diagonal partition is a geometric series).**

$$x>0 \Rightarrow W(x,x) = \frac{1}{1-\operatorname{exp}(-\sqrt{5}x)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/DiagonalCollapse.diagonal_partition_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real diagonal parameter, sum the two-face weight over all canonical nonadjacent Fibonacci words. Binet's formula turns the difference between the expansion and contraction powers into sqrt(5) times the decoded Fibonacci value. The canonical word equivalence then reindexes the sum by the natural numbers, where it is exactly the geometric series with ratio exp(-sqrt(5) x). The positivity hypothesis makes the convergence condition explicit; it was implicit in the source atom's analytic notation.

The pinned library was searched first. It contains the canonical Zeckendorf equivalence, Binet's formula, and the real geometric-series summation theorem, but no declaration combining them into this diagonal identity. The proof is therefore a new composition of library results rather than a wrapper around an existing combined theorem. The numerical window check reported with the source atom is not needed because the deposited equality is exact.

## References

- Truth anchor: `D5/S3/Analytic/DiagonalCollapse.diagonal_partition_collapse`
- Dependency: [D5/S0/Conventions/WDigits](../../S0/Conventions/WDigits.md)
