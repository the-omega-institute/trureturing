# Disjoint two-term sums and directed differences

## Abstract

Shared endpoints give the correction from directed differences to disjoint two-term sums.

**Theorem 1.1 (Endpoint correction for the degree-two mass).**

$$R_{2} = A - 2 \sum_{i} \left(w_{i}\right)^{2} C_{i} + \sum_{i,j \neq i} \left(w_{i}\right)^{2} \left(w_{j}\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DegreeTwoResidualDifferenceEnergy.degree_two_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a finite index set with real frequencies g and real weights w. Take a nonnegative resolution η. The mass R with subscript two sums products of weighted multinomial coefficients over ordered pairs of degree-two count vectors with disjoint supports and frequency-sum discrepancy at most η.

Let A be the near-collision mass on the directed edges (i,j) with i≠j, using frequency g(i)−g(j), weight w(i)w(j), and resolution η. Let C with subscript i be the near-collision mass of the original spectrum with index i deleted, with the same resolution and including the diagonal.

Expanding each multinomial coefficient by its ordered words turns a pair of sums g(i)+g(k) and g(j)+g(l) into the two directed differences g(i)−g(j) and g(l)−g(k). Disjointness excludes the shared endpoints i=l and j=k in addition to the two forbidden loops. Subtract each shared-endpoint contribution and add their intersection once. At an intersection both directed edges are equal and their discrepancy is zero.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/DegreeTwoResidualDifferenceEnergy.degree_two_residual`
- Dependency: [D5/S3/Fourier/Concentration/FiniteSincCollisionMoment](FiniteSincCollisionMoment.md)
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../../Quantum/Entanglement/OccupancyWordSectors.md)
