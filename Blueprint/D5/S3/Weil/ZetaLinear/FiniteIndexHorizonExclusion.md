# Finite-Index Horizon Exclusion

## Abstract

A uniform finite inclusion-index bound excludes noncritical zeta zeros.

**Theorem 1.1 (A finite horizon bound forces critical-line location).**

$$\begin{gathered}\forall inclusionIndex: \mathbb{R} \to \mathbb{R}, bound \in \mathbb{R},\\{}(\forall omega \in \mathbb{R}, 0 < omega \Rightarrow omega < criticalAbscissa \Rightarrow \operatorname{inclusionIndex}(omega) \leq bound) \land\\{}(\forall \rho \in \mathbb{C}, \operatorname{IsNontrivialZero}(\rho) \Rightarrow\\{}criticalAbscissa < \operatorname{Re}(\rho) \Rightarrow \forall omega \in \mathbb{R}, 0 < omega \Rightarrow omega < \operatorname{criticalDisplacement}(\rho) \Rightarrow\\{}\operatorname{horizonEffectiveIndex}(\operatorname{singletonMatrix}(\frac{omega}{\operatorname{criticalDisplacement}(\rho)})) \leq \operatorname{inclusionIndex}(omega)) \Rightarrow\\{}\forall \rho \in \mathbb{C}, \operatorname{IsNontrivialZero}(\rho) \Rightarrow \operatorname{Re}(\rho) = criticalAbscissa.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/FiniteIndexHorizonExclusion.finite_index_horizon_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inclusionIndex function models the information index of the observer inclusion at each positive depth below the critical abscissa, and bound is its uniform finite upper bound.

For a right-side nontrivial zero rho, the controlled matrix is the one-by-one Hankel matrix with entry omega divided by the canonical criticalDisplacement of rho. Its effective index is the reciprocal singular factor, which exceeds every fixed bound near the horizon.

Repository reflection transports any left-side nontrivial zero to the excluded right side, so every nontrivial zero has critical real part.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/FiniteIndexHorizonExclusion.finite_index_horizon_exclusion`
- Dependency: [D5/S3/Weil/Pick/HorizonEffectiveIndex](../Pick/HorizonEffectiveIndex.md)
- Dependency: [D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening](ReflectedZeroModePhaseFlattening.md)
