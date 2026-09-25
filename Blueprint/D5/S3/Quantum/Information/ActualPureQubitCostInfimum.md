# Actual pure-qubit cost infimum

## Abstract

The full finite affine-readout pure-qubit cost infimum has quadratic coefficient one quarter of the weighted score-square projection residual.

**Theorem 1.1 (Exact quadratic infimum coefficient).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite positive probability data, a nonzero centered direction, and at least three distinct scores, the residual is positive and the normalized infimum excess tends to one quarter of that residual as real positive radii tend to zero. Repeated and zero individual scores are allowed. Cubic approximate minimizers suffice; no optimum is assumed attained. This result makes no two-score attainment or unrestricted CPTP processor equivalence claim.

The lower bound uses the joint limit of feasible rank-two coefficients: positivity, normalization, and the spectral cost equation exclude a positive limiting transverse parameter when three scores are distinct. The remaining diagonal coefficients converge to the normalized weighted score squares. An exact matching inequality then gives the quadratic lower coefficient. The rank-one branch has a fixed positive cost gap, and a smooth family of actual programs supplies the matching upper bound.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.result`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitFisherRank](ActualPureQubitFisherRank.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitUpperFamily](ActualPureQubitUpperFamily.md)
