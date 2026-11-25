# Rational joint states with a maximally mixed endpoint

## Abstract

An explicit arithmetic witness for a maximally mixed qubit marginal.

**Theorem 1.1 (Rank two for a maximally mixed endpoint and a rational Bloch length).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/RationalQubitMixedEndpoint.rational_rank_two_of_maximally_mixed_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/RationalQubitMixedEndpoint.rational_rank_two_of_maximally_mixed_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c be a rational Bloch vector of rational length r with 0 < r < 1. Then half the identity and the trace-one Bloch matrix for c are partial traces of a positive semidefinite joint matrix of rank exactly two whose entries have rational real and imaginary parts.

Write 1 − r² as four rational squares p² + q² + s² + t² using Lagrange's theorem. Reorder so that D = p² + q² is positive. The vector (D, ps − qt, pt + qs) has squared length D(1 − r²), while (p, q, 0) has squared length D. A rational reflection carries the third coordinate unit vector to c/r. Apply it to (p, q, 0) to obtain v perpendicular to c without changing its squared length. These vectors satisfy the two witness equations of the rational qubit projector construction.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/RationalQubitMixedEndpoint.rational_rank_two_of_maximally_mixed_endpoint`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/RationalQubitProjector](RationalQubitProjector.md)
