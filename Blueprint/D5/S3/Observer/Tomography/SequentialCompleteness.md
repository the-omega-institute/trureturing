# Sequential Completeness

## Abstract

Sequential readout completeness is equivalent to a trivial residual and full visible span.

**Theorem 1.1 (Sequential completeness, zero residual, and full visible span).**

$$\forall d\in \mathbb{N}, \operatorname\left({NeZero}, d\right), A: \operatorname{Type},\\{}E: A \to \operatorname{Herm}_{d}^{0},\\{}V_{0} = span\left(\mathbb{R}, (E_{i}: i\in A)\right), V = \mathbb{R}I + V_{0},\\{}N = V^{\perp},\\{}\operatorname\left({Injective}, (\rho: DensityState\left(Fin\left(d\right)\right) \mapsto (i: A \mapsto \Re Tr\left(matrix\left(\rho\right) E_{i}\right)))\right) \iff N = \{0\} \iff V = \operatorname{Herm}_{d}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/SequentialCompleteness.sequential_completeness_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The allowed readout effects are centered Hermitian directions. Their real span is combined with the scalar identity line to construct the visible Hermitian space, and the residual is its orthogonal complement.

The canonical density-state signature is injective exactly when the centered effect span is full; finite-dimensional orthogonality then identifies a zero residual with a full visible span.

## References

- Truth anchor: `D5/S3/Observer/Tomography/SequentialCompleteness.sequential_completeness_criterion`
- Dependency: [D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence](../../Quantum/Tomography/InformationalCompletenessEquivalence.md)
