# All Future Statistics Sufficiency

## Abstract

The canonical predictive projection is equivalent to all future statistics.

**Theorem 1.1 (The predictive coordinate determines exactly every future expectation).**

$$\forall d, r\in \mathbb{N}, \forall H: \operatorname{End}(\operatorname{Herm}_{d}^{0}), \forall E: \operatorname{Fin}(r + 1) \to \operatorname{Herm}_{d}^{0}, \forall \rho, \sigma\in \operatorname{Herm}_{d}^{0}, \operatorname{predictiveProjection}(H, E, \rho) = \operatorname{predictiveProjection}(H, E, \sigma) \iff \forall k\in \mathbb{N}, \forall a\in \operatorname{Fin}(r + 1), \langle\rho, H^{k}(E_a)\rangle = \langle\sigma, H^{k}(E_a)\rangle.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency.all_future_statistics_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Work on the real vector space of traceless Hermitian matrices. A finite centered effect family and its finite Heisenberg iterates generate the final predictive subspace.

The predictive coordinate is the canonical orthogonal projection onto that all-iterate span. Two centered state coordinates have equal projections exactly when every iterated centered effect has the same expectation on both coordinates.

The proof imports the frozen carrier, predictive span, and projection. Projection equality is converted to orthogonality of the state difference, and span induction converts this to the complete family of future expectation equalities.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency.all_future_statistics_sufficiency`
- Dependency: [D5/S3/Quantum/Fibers/MinimalPredictiveSummary](MinimalPredictiveSummary.md)
