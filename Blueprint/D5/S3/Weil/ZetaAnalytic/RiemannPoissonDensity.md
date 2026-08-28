# Riemann Poisson Density

## Abstract

The shifted-xi phase density is the Poisson smoothing of its zero-counting measure.

**Theorem 1.1 (Riemann Poisson-density theorem).**

$$\forall Z \in \operatorname{ZeroData}\left(\right), omega \in \mathbb{R},\; \left(0 < omega \land \left(\operatorname{RiemannHypothesis}\left(\right) \land \left(\forall x \in \mathbb{R},\; 0 < omega \Rightarrow \left(\operatorname{RiemannHypothesis}\left(\right) \Rightarrow \operatorname{phaseDensity}\left(omega, x\right) = \sum_{n\in\mathbb{N}} \operatorname{multiplicity}\left(Z, n\right) \cdot \operatorname{poissonKernel}\left(omega, x - \operatorname{im}\left(\operatorname{zero}\left(Z, n\right)\right)\right)\right)\right)\right)\right) \Rightarrow (x \mapsto \operatorname{phaseDensity}\left(omega, x\right)) = (x \mapsto \operatorname{poissonSmooth}\left(omega, \operatorname{zeroCountingMeasure}\left(Z\right), x\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaAnalytic/RiemannPoissonDensity.riemann_poisson_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The phase density is constructed from the logarithmic derivative of the canonical entire xi reading. The counting measure is built independently from a duplicate-free exhaustive zero enumeration.

Under the critical-line hypothesis and the preceding logarithmic-derivative zero expansion, integration against the weighted sum of Dirac masses is exactly the sum of translated Poisson kernels.

## References

- Truth anchor: `D5/S3/Weil/ZetaAnalytic/RiemannPoissonDensity.riemann_poisson_density`
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)
