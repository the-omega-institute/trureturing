# Effect-weighted tester incompatibility

## Abstract

An effect-weighted joint cover bounds the incompatibility of finite one-step testers.

Let A and B be finite one-step testers with positive output dimension and input density matrices ρ and σ. The effects are positive semidefinite and their respective sums are I ⊗ ρ and I ⊗ σ.

**Theorem 1.1 (Positive weighted joint cover).**

$$\begin{aligned}0&\leq\varepsilon\leq\min(a^{-1},b^{-1})\\C_{jk}&=(1+a\varepsilon^{2})\frac{\beta_{k}}{b}A_{j}+(1+b\varepsilon^{2})\frac{\alpha_{j}}{a}B_{k}-\varepsilon(A_{j}B_{k}+B_{k}A_{j})\\H&=(1+a\varepsilon^{2})\rho+(1+b\varepsilon^{2})\sigma-\varepsilon(\rho\sigma+\sigma\rho)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SedlakWeightedTesterCover.weightedJointCover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose nonnegative upper bounds αⱼ and βₖ in the positive operator order for the effects. Their totals a and b are positive. The cover entries use the normalized weights βₖ/b and αⱼ/a to distribute the two effects before subtracting the symmetrized product. Completing a positive sandwich with the opposite lifted normalization state proves marginal domination. The displayed H is the input normalization of the joint sum.

**Theorem 1.2 (Overlap and operator-norm bound).**

$$\begin{aligned}\delta&=\Re \operatorname{tr}\left(\rho\sigma\right)\\a&=\sum_{j}\left\lVert A_{j} \right\rVert\quad b=\sum_{k}\left\lVert B_{k} \right\rVert\\t&=2-\frac{\delta^{2}}{a+b}\\\left(R_{t}\right)\left(A, B\right)&\leq 1-t^{-1}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SedlakWeightedTesterCover.opNormRobustnessBound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the Euclidean operator norm of each effect for its weight. A positive effect is bounded in operator order by its operator norm times the identity. At ε = δ/(a + b), the cover has normalization trace t. Dividing the cover and using its marginal slacks yields a feasible mixing weight 1 − 1/t.

**Theorem 1.3 (Invariance under proportional effect refinement).**

$$\sum_{j,l}\left\lVert \theta_{jl}A_{j} \right\rVert=\sum_{j}\left\lVert A_{j} \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SedlakWeightedTesterCover.sum_effect_norm_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each effect Aⱼ, take finitely many nonnegative real coefficients θⱼₗ summing to one. Absolute homogeneity of the operator norm preserves the total when Aⱼ is replaced by the family θⱼₗ Aⱼ. The resulting denominator is the same for either tester before and after proportional refinements.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakWeightedTesterCover.opNormRobustnessBound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakWeightedTesterCover.sum_effect_norm_refinement`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakWeightedTesterCover.weightedJointCover`
- Dependency: [D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality](SedlakMaximalTesterOrthogonality.md)
