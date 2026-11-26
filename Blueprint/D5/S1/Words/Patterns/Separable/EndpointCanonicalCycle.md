# Canonical cycle parsing and original coordinates

## Abstract

Original emitted coordinates agree with the canonical marked-cycle test on every sufficiently long successful bounded history.

For an actual permutation avoiding 2413 and 3142, the canonical parser recovers its signed least proper cut. It emits a strictly shorter left factor or removes a strictly shorter right factor, retaining the actual factorization and residual. Ties and unsuccessful recursions do not count as successful parses.

On a successful bounded tuple, erasing the cutoffs retains the same actual marked cycles and remaining permutation. For a fixed number of cycles k, integer target e, and natural bounds K,H, write A(n,pi) for successful canonical parsing followed by the literal test i-pi(i)=e at an emitted position. Q(p) is the recursive erased-tuple hit test at e.

**Theorem 1.1 (Eventual literal agreement on successful bounded histories).**

$$Eventually n, \forall p,pi, \operatorname{Event}\left(p, n, pi\right) implies \operatorname{iff}\left(\operatorname{A}\left(n, pi\right), \operatorname{Q}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointCanonicalCycle.actualCanonicalFirstKLiteralHit_eventually_agrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual embedding shifts positions by the emitted count and shifts values by the advance in the lower-value origin. Their difference is the recursively accumulated mark increment. Direct emissions retain the literal local occupancy test. The residual size bound excludes a skew emission at the specified offset, uniformly over the finitely many bounded tuples.

The result compares the original points only in the emitted prefix. It does not test removed or residual points, assert agreement on parser failures, or make the cutoff uniform in k or e.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointCanonicalCycle.actualCanonicalFirstKLiteralHit_eventually_agrees`
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries](EndpointCycleHazardSeries.md)
