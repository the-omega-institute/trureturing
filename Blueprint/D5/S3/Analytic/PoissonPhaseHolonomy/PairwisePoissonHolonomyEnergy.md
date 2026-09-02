# Pairwise Poisson Phase-Holonomy Energy

## Abstract

The pairwise Poisson phase-holonomy integral is nonnegative, detects equal heights, and is invariant under common height translation.

**Theorem 1.1 (Poisson phase-holonomy energy has the rational closed form).**

$$\forall deltaI \in \operatorname{Real}\left(\right), deltaJ \in \operatorname{Real}\left(\right), gammaI \in \operatorname{Real}\left(\right), gammaJ \in \operatorname{Real}\left(\right),\; \left(0 < deltaI \land 0 < deltaJ\right) \Rightarrow \left(poissonPhaseHolonomyEnergy\left(deltaI, deltaJ, gammaI, gammaJ\right) = \frac{(poissonHeightDifference\left(gammaI, gammaJ\right))^{2}}{pi \times poissonTransverseDepthSum\left(deltaI, deltaJ\right) \times ((poissonTransverseDepthSum\left(deltaI, deltaJ\right))^{2} + (poissonHeightDifference\left(gammaI, gammaJ\right))^{2})} \land \left(0 \le poissonPhaseHolonomyEnergy\left(deltaI, deltaJ, gammaI, gammaJ\right) \land \left(\left(poissonPhaseHolonomyEnergy\left(deltaI, deltaJ, gammaI, gammaJ\right) = 0 \Rightarrow gammaI = gammaJ\right) \land \left(\left(gammaI = gammaJ \Rightarrow poissonPhaseHolonomyEnergy\left(deltaI, deltaJ, gammaI, gammaJ\right) = 0\right) \land \left(\forall c \in \operatorname{Real}\left(\right),\; poissonPhaseHolonomyEnergy\left(deltaI, deltaJ, gammaI + c, gammaJ + c\right) = poissonPhaseHolonomyEnergy\left(deltaI, deltaJ, gammaI, gammaJ\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PoissonPhaseHolonomy/PairwisePoissonHolonomyEnergy.pairwise_poisson_holonomy_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive transverse depths, a is their sum and d is the difference of the two real phase heights. The energy named in the formula is exactly one over two pi times the full real-line integral of the squared norm of the explicit complex Poisson swap curvature.

The five result leaves are the rational integral evaluation, nonnegativity, each direction of the zero-height criterion, and invariance under every common real translation.

This conditional analytic theorem does not assert that off-critical zeros exist and does not identify this curvature with the repository's stable residual swap curvature.

## References

- Truth anchor: `D5/S3/Analytic/PoissonPhaseHolonomy/PairwisePoissonHolonomyEnergy.pairwise_poisson_holonomy_energy`
