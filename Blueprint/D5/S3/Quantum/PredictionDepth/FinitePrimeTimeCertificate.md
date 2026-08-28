# Finite Prime-Time Certificate

## Abstract

A complete natural-indexed quantum effect family has a finite dimension-bounded certificate.

**Theorem 1.1 (Complete effects have a finite prime-time certificate).**

$$\forall d\in \mathbb{N}, \operatorname{NeZero}\left(d\right),\\{}E: \mathbb{N}\times\mathbb{N} \to \operatorname{Herm}_{d, 0},\\{}\operatorname{span}\left(\mathbb{R}, (E(p, t): p, t\in \mathbb{N})\right) = \operatorname{Herm}_{d, 0} \Rightarrow\\{}\exists J: \operatorname{Finset}\left(\mathbb{N}\times\mathbb{N}\right), \operatorname{card}\left(J\right) \leq d^{2}-1 \land\\{}\operatorname{span}\left(\mathbb{R}, (E(p, t): (p, t)\in J)\right) = \operatorname{Herm}_{d, 0} \land\\{}\forall \rho, \sigma: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), (\forall (p, t)\in J, \Re \operatorname{Tr}\left(\operatorname{matrix}\left(\rho\right) E\left(p, t\right)\right) = \Re \operatorname{Tr}\left(\operatorname{matrix}\left(\sigma\right) E\left(p, t\right)\right)) \Rightarrow \rho = \sigma.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/FinitePrimeTimeCertificate.finite_prime_time_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first coordinate of each natural pair is the observer index and the second is time. No arithmetic-primality predicate is imposed on the first coordinate.

If the full family spans the real traceless Hermitian carrier, finite-dimensional basis extraction selects concrete pairs whose number is at most the carrier dimension d squared minus one.

The selected effects still span the full carrier. The difference of two density states is a traceless Hermitian coordinate, so equality of all selected real trace expectations forces the states to agree.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/FinitePrimeTimeCertificate.finite_prime_time_certificate`
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../Divergence/QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence](../Fibers/TraceZeroReadoutOrthogonalEquivalence.md)
