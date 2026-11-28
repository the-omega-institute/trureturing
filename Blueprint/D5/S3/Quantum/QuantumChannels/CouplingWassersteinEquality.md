# Equality in trace-ground coupling transport

## Abstract

For order one with the pure-state trace ground, equality with half the trace norm is equivalent to a common positive semidefinite remainder and a finite family of moving pairs. In each pair the two projectors use the same positive and negative spectral vectors with swapped amplitudes.

**Definition 1.1 (The shared remainder and moving pairs).**

$$\forall n: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall h: \operatorname{IsHermitian}\left(\rho - \sigma\right), (\operatorname{HasSpectralCertificate}\left(\rho, \sigma, h\right)) \Leftrightarrow (\exists R: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \exists m: \mathbb{N}, \exists w: \operatorname{Fin}\left(m\right) \to \mathbb{R}, \exists t: \operatorname{Fin}\left(m\right) \to \mathbb{R}, \exists u: \operatorname{Fin}\left(m\right) \to \operatorname{UnitVector}\left(n\right), \exists v: \operatorname{Fin}\left(m\right) \to \operatorname{UnitVector}\left(n\right), (\operatorname{PosSemidef}\left(R\right)) \land ((\forall i: \operatorname{Fin}\left(m\right), (0 < w\left(i\right)) \land ((0 < t\left(i\right)) \land ((t\left(i\right) \le 1) \land ((\operatorname{val}\left(u\left(i\right)\right) \in \operatorname{positiveSubspace}\left(\rho - \sigma, h\right)) \land (\operatorname{val}\left(v\left(i\right)\right) \in \operatorname{negativeSubspace}\left(\rho - \sigma, h\right)))))) \land ((\rho = R+\sum_{i\in \operatorname{Fin}\left(m\right)} \operatorname{ofReal}\left(w\left(i\right)\right)\cdot \operatorname{rankOneDensity}\left(\operatorname{ofReal}\left(\operatorname{sqrt}\left(\frac{1+t\left(i\right)}{2}\right)\right)\cdot \operatorname{val}\left(u\left(i\right)\right)+\operatorname{ofReal}\left(\operatorname{sqrt}\left(\frac{1-t\left(i\right)}{2}\right)\right)\cdot \operatorname{val}\left(v\left(i\right)\right)\right)) \land (\sigma = R+\sum_{i\in \operatorname{Fin}\left(m\right)} \operatorname{ofReal}\left(w\left(i\right)\right)\cdot \operatorname{rankOneDensity}\left(\operatorname{ofReal}\left(\operatorname{sqrt}\left(\frac{1-t\left(i\right)}{2}\right)\right)\cdot \operatorname{val}\left(u\left(i\right)\right)+\operatorname{ofReal}\left(\operatorname{sqrt}\left(\frac{1+t\left(i\right)}{2}\right)\right)\cdot \operatorname{val}\left(v\left(i\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CouplingWassersteinEquality.HasSpectralCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proof h establishes that Δ = ρ − σ is Hermitian and determines the strict spectral subspaces of Δ. The predicate takes both marginals. The map val takes a unit vector to its underlying complex vector. The rankOneDensity map sends z to zz*. The square roots are real. The map ofReal sends each amplitude and each weight to ℂ before it acts on the corresponding vector or matrix.

**Theorem 1.2 (Equality with half the trace norm).**

$$\forall n: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (0 < n) \Rightarrow (\forall p: \operatorname{PosSemidef}\left(\rho\right), (\operatorname{trace}\left(\rho\right) = 1) \Rightarrow (\forall q: \operatorname{PosSemidef}\left(\sigma\right), (\operatorname{trace}\left(\sigma\right) = 1) \Rightarrow ((\operatorname{wasserstein}\left(\rho, \sigma\right) = \frac{\operatorname{traceNorm}\left(\rho - \sigma\right)}{2}) \Leftrightarrow (\operatorname{HasSpectralCertificate}\left(\rho, \sigma, \operatorname{hermitianSub}\left(p, q\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CouplingWassersteinEquality.wasserstein_eq_traceNorm_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* E. Beatty; D. Stilck França (2025). *Order p quantum Wasserstein distances from couplings*. DOI: [10.1007/s00023-025-01557-z](https://doi.org/10.1007/s00023-025-01557-z). URL: <https://arxiv.org/abs/2402.16477v2>.

*Commentary.*

The question following Eq. (62) asks when the dual-norm lower bound is attained. At order one with the pure trace ground of Eq. (81), Proposition 26 and Eq. (82) identify that dual norm with half the trace norm. The distance is the infimum over the original countable plans of Definitions 8–9. Dropping zero weights or enumerating and padding with zeros preserves the two marginals and cost. The term hermitianSub(p,q) proves that ρ − σ is Hermitian from the positive semidefinite hypotheses p and q.

Proposition 16 establishes finite attainment in the paper. Here the two marginal matrices and the cost form a joint moment. Finite partial sums with leftover mass on a fixed pure pair put every countable plan moment in the closed convex hull of the pure-pair moment set. The moment set and its finite-dimensional convex hull are compact. The spectral product plan makes the fixed-marginal slice nonempty. Minimizing its cost coordinate and enumerating the resulting finite convex combination gives an optimizer for the original infimum.

For necessity, use the Hermitian sign of the difference in a finite optimizer. Group the stationary entries into the same positive semidefinite sum R in both marginals. Reindex the remaining positive-weight entries by Fin m. Each moving pair has parameter equal to its ground distance and has the stated swapped amplitudes in the strict spectral subspaces.

For sufficiency, assign the nonnegative eigenvalues of R as weights of stationary pairs, then add the specified moving pairs. The extremal eigenspaces of the sign are orthogonal. This gives unit vectors in the two displayed projectors and gives ground distance t for each moving pair. Taking the trace of a marginal gives total weight one. Every positive-weight entry attains the sign test, so the countable-plan infimum equals half the trace norm. For equal marginals one can take m equal to zero and R equal to the common matrix.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/CouplingWassersteinEquality.HasSpectralCertificate`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CouplingWassersteinEquality.wasserstein_eq_traceNorm_iff`
- Dependency: [D5/S3/Quantum/Foundation/FiniteHermitianSign](../Foundation/FiniteHermitianSign.md)
- Dependency: [D5/S3/Quantum/Foundation/TrigonometricMomentGap](../Foundation/TrigonometricMomentGap.md)
- Dependency: [D5/S3/Quantum/GleasonComplexRepresentation](../GleasonComplexRepresentation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation](CouplingWassersteinTriangleRefutation.md)
