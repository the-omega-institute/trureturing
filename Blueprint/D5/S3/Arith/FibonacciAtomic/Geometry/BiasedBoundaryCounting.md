# The Actual Boundary Spectral Count

## Abstract

Let e and k be paired real Hilbert bases of the actual centered boundary space G0 and effective edge space K. Their positive covariance eigenvalues mu are nonincreasing and tend to zero. Their reciprocals are nondecreasing, tend to infinity, and give the original boundary operator graph on each basis vector.

**Definition 1.1 (modeSpace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.modeSpace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.modeSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real Hilbert basis e and a finite index set s, modeSpace(e,s) is the real linear span of the selected basis vectors. Empty selections give the zero subspace.

**Definition 1.2 (modeProjection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.modeProjection`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.modeProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For that same e and s, modeProjection(e,s) is the finite sum of the rank-one maps u to inner(e(i),u) times e(i). It acts on every vector in the same real Hilbert carrier.

**Definition 1.3 (positiveCount).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.positiveCount`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.positiveCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

positiveCount(mu,lam) is the finite-set cardinality of all natural indices i with reciprocal mu(i) at most lam. Finiteness for the actual spectral family is proved in the theorem, so this cardinality counts every occurrence of a repeated eigenvalue.

**Definition 1.4 (strictCount).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.strictCount`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.strictCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

strictCount(mu,lam) uses the strict condition reciprocal mu(i) less than lam, preserving the distinction at an eigenvalue threshold.

**Definition 1.5 (positiveEigenvalue).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.positiveEigenvalue`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.positiveEigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

positiveEigenvalue(mu,j) is the reciprocal of mu(j-1); the theorem uses it only for j at least one, exactly the source indexing convention.

**Definition 1.6 (B).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.B`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B is the single real constant 2 times goldenRatio divided by the original right-child mass b. The theorem proves that it also equals 2 times goldenRatio cubed.

**Definition 1.7 (fullModeSpace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.fullModeSpace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.fullModeSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fullModeSpace(e,s,includeConstant) is the image of the selected positive span in the original boundary G, together with the actual constant line if and only if includeConstant holds. The theorem uses the inclusive condition zero at most lam and the strict condition zero less than lam respectively.

**Theorem 1.8 (The Actual Boundary Spectral Count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.actual_spectral_counting`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.actual_spectral_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let e and k be paired real Hilbert bases of the actual centered boundary space G0 and effective edge space K. Their positive covariance eigenvalues mu are nonincreasing and tend to zero. Their reciprocals are nondecreasing, tend to infinity, and give the original boundary operator graph on each basis vector.

A finite set of mode indices determines its span and its finite orthogonal coefficient projection. The range is exactly that span and its dimension is the number of indices. Every occurrence of a repeated eigenvalue contributes its own basis index. For every real threshold, both the inclusive condition 1/mu(i) at most the threshold and the strict condition 1/mu(i) below the threshold select finite sets. Both boundary and edge projections have exactly those ranges. Membership is equivalent, for every vector, to vanishing of every coefficient outside the selected set. The corresponding boundary and edge spans have the inclusive and strict counts as their exact dimensions.

For a nonnegative threshold, the full inclusive boundary cutoff is the sum of the positive cutoff and the constant line. These summands are disjoint because the positive modes have mean zero and the mean of constG(c) is c. Its dimension is therefore exactly one plus the positive count, including at threshold zero. Both positive counts at zero are zero. The full strict cutoff includes the constant line only for a strictly positive threshold; at zero its dimension is zero. Negative thresholds also exclude the constant line.

For the upper comparison, the stopping average maps an inclusive low spectral span to the original centered stopping-cylinder space. Every vector of the spectral span belongs to the original form domain and has minimum energy at most the spectral threshold times its squared norm. If its stopping average vanished, the original squared residual estimate would bound its squared norm by phi times t times that energy. Choosing t=1/(2 phi times the threshold) forces the vector to vanish. The resulting injection bounds the positive count by k(t)-1.

For the lower comparison, project the original centered stopping-cylinder trial space into the strict low spectral span. A vector in the kernel has spectral support at or above the threshold, so the whole-domain spectral form estimate bounds its energy from below. The original finite stopping extension bounds the minimum energy strictly below the same threshold times its squared norm when t=1/(b times the threshold). These inequalities force a zero vector. The strict spectral count is therefore at least k(t)-1. No equality between the chosen extension energy and the least energy is assumed.

Set B=2 phi/b=2 phi cubed, where b=phi to the power minus two. The actual eigenvalue gap gives zero positive inclusive count for every nonnegative threshold below 1/phi. The stopping cardinality inequalities give Nplus(lam) at most B times lam for all nonnegative lam and give both strict and inclusive counts at least b times lam minus one for lam greater than 1/b. For lam at least 2/b this lower bound is at least b times lam divided by two.

The original positive eigenvalue index starts at one: lambda(j)=1/mu(j-1) for j at least one. The first j indices lie in its inclusive cutoff, giving j/B at most lambda(j). Its strict cutoff contains at most j-1 indices, and the strict lower bound yields lambda(j) at most j/b. These arguments keep equality at the inclusive threshold and allow repeated eigenvalues throughout.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.B`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.actual_spectral_counting`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.fullModeSpace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.modeProjection`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.modeSpace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.positiveCount`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.positiveEigenvalue`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting.strictCount`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySpectralForm](BiasedBoundarySpectralForm.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrialEnergy](BiasedBoundaryTrialEnergy.md)
