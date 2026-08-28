# Future Statistics and the Infinite Operator System

## Abstract

Future operator statistics are exactly the annihilator of the generated system.

**Theorem 1.1 (Future statistics characterize the infinite-system annihilator).**

$$\begin{gathered}\forall d, \operatorname{Finite}\left(d\right), [\operatorname{DecidableEq}(d)],\\{}\phi: \operatorname{QuantumChannel}\left(d, d\right), \phi^{*}: \operatorname{CompletelyPositiveMap}\left(\operatorname{Matrix}\left(d, d, \mathbb{C}\right), \operatorname{Matrix}\left(d, d, \mathbb{C}\right)\right), \phi^{*}(I) = I,\\{}\forall X, A: \operatorname{Matrix}\left(d, d, \mathbb{C}\right), \operatorname{Tr}(\phi(X) A) = \operatorname{Tr}(X \phi^{*}(A)),\\{}S_{0}: \operatorname{OperatorSystem}\left(\operatorname{Hermitian}\left(\operatorname{Matrix}\left(d, d, \mathbb{C}\right)\right)\right), \rho, \sigma: \operatorname{DensityState}\left(d\right),\\{}S_{\infty} := \operatorname{span}_{\mathbb{R}}(\left\{(\phi^{*})^{k}(E) \mid k\in \mathbb{N}, E\in S_{0}\right\}),\\{}(\forall k\in \mathbb{N}, \operatorname{operatorSystemReadout}\left(S_{0}, \operatorname{evolvedState}\left(\phi, k, \rho\right)\right) = \operatorname{operatorSystemReadout}\left(S_{0}, \operatorname{evolvedState}\left(\phi, k, \sigma\right)\right))\\{}\Leftrightarrow\\{}\forall A\in S_{\infty}, \operatorname{Tr}((\rho-\sigma)A) = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FutureStatisticsEquivalence.future_statistics_iff_annihilates_infinite_system` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The states are positive trace-one matrices on a finite complex matrix carrier. The Schrödinger map is completely positive and trace-preserving, while its Heisenberg dual is completely positive, unital, and satisfies the displayed trace-duality identity.

The initial operator system is a real subspace of the full Hermitian carrier containing the identity. The infinite prediction system is the real span of every finite Heisenberg iterate of every initial effect.

Equality of the complete initial-system readout after every finite channel iterate is equivalent to zero trace pairing of the state difference with every effect in that generated system.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/FutureStatisticsEquivalence.future_statistics_iff_annihilates_infinite_system`
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../Divergence/QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/Fibers/OperatorSystemTowerStability](OperatorSystemTowerStability.md)
