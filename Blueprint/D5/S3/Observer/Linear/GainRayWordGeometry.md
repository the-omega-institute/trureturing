# Three source directions in every mixed word

## Abstract

Three source directions in every mixed word

**Theorem 1.1 (Every mixed cumulative trajectory spans at least three dimensions).**

Lean statement: `D5/S3/Observer/Linear/GainRayWordGeometry.mixed_cumulative_span`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayWordGeometry.mixed_cumulative_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every chronological Boolean word w containing both false and true, the real span of acquisition(take i w), for all initial-inclusive i in Fin(length(w)+1), has dimension at least three. Both switch orientations are included. If M occurs first and its initial block has positive length k, the cumulative matrices include I,M,J*M^k. The existing frozen Fibonacci block identity gives M^k=a*I+b*M with a nonnegative and b positive; the two off-diagonal entries of J*M^k differ by b. If J occurs first, the trajectory includes I,J and M*J^k. According to k modulo two, the third matrix is M or M*J, each outside the span of I,J. The proof uses the actual cumulative prefixes of the same literal word.

**Theorem 1.2 (Consecutive cumulative matrices are not proportional).**

Lean statement: `D5/S3/Observer/Linear/GainRayWordGeometry.cumulative_not_proportional_adjacent`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayWordGeometry.cumulative_not_proportional_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every chronological Boolean word w, every i less than its action length, and every real c, acquisition(take(i+1,w)) differs from c times acquisition(take(i,w)). Every native cumulative matrix is invertible by its signed determinant. Proportionality would force the next M or J to be scalar, contrary to its off-diagonal entry one.

**Theorem 1.3 (A matrix ray occupies at most half the read positions rounded up).**

Lean statement: `D5/S3/Observer/Linear/GainRayWordGeometry.cumulative_proportionality_card`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayWordGeometry.cumulative_proportionality_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word w and every real auxiliary matrix L, the number of initial-inclusive indices i whose actual cumulative matrix equals c*L for some real c is at most (length(w)+2)/2 using natural division. No two such indices are consecutive. The map from such an index to its natural value divided by two is injective, and its image lies below this ceiling. The statement includes L=0 and every pure or mixed word.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayWordGeometry.cumulative_not_proportional_adjacent`
- Truth anchor: `D5/S3/Observer/Linear/GainRayWordGeometry.cumulative_proportionality_card`
- Truth anchor: `D5/S3/Observer/Linear/GainRayWordGeometry.mixed_cumulative_span`
- Dependency: [D5/S3/Observer/Linear/GainRayHistory](GainRayHistory.md)
