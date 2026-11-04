# Actual fourth graph estimate

## Abstract

Actual fourth graph estimate

**Theorem 1.1 (Finite even sums in the actual physical graph).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfFourthGraph.finite_even_physical_x2_graph_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfFourthGraph.finite_even_physical_x2_graph_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real sequence d and every cutoff N, let F be the finite sum of d(k) psi_(2k). Then x^(15/2) F(x)^2 is integrable on x>0 and its integral is at most 648^2 times the sum over k<N of (k+1)^4 d(k)^2.

The supplier proof is reused from commit c9332472. Two applications of the actual physical Jacobi recurrence, exact polynomial orthogonality, and a three-term square estimate establish the graph bound. No assumed matrix enclosure, coefficient completeness or physical-domain surjectivity is used. The bound is consumed by the actual weighted synthesis map; imported attribution and license notices are retained.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfFourthGraph.finite_even_physical_x2_graph_bound`
