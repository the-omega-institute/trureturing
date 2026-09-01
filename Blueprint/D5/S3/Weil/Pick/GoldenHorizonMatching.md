# Golden Horizon Matching

## Abstract

The golden effective index characterizes six equivalent rank-one channel conditions.

**Theorem 1.1 (The golden effective index characterizes rank-one channel data).**

$$\begin{aligned}\forall \delta \in \mathbb{R}, \omega \in \mathbb{R},\\{}0 < \delta \land 0 < \omega \land \omega < \delta \Rightarrow\\{}let \sigma = \frac{\omega}{\delta};\\{}let H: \mathbb{R}^{1 \times 1} = \operatorname{matrix1x1}\left(\sigma\right);\\{}let I_{hor} = \operatorname{horizonEffectiveIndex}\left(H\right);\\{}let r = \operatorname{artanh}\left(\sigma\right);\\{}let \alpha = \operatorname{cosh}\left(r\right);\\{}let \beta = \operatorname{sinh}\left(r\right);\\{}let D_{KL} = \operatorname{log}\left(I_{hor}\right);\\{}(I_{hor} = \varphi^{2} \Leftrightarrow 1 - \sigma^{2} = \varphi^{-2}) \land\\{}(I_{hor} = \varphi^{2} \Leftrightarrow \sigma^{2} = \varphi^{-1}) \land\\{}(I_{hor} = \varphi^{2} \Leftrightarrow \left|\alpha\right|^{2} = \varphi^{2}) \land\\{}(I_{hor} = \varphi^{2} \Leftrightarrow \left|\beta\right|^{2} = \varphi) \land\\{}(I_{hor} = \varphi^{2} \Leftrightarrow D_{KL} = 2 \times \operatorname{log}\left(\varphi\right)) \land\\{}(I_{hor} = \varphi^{2} \Leftrightarrow \frac{\omega}{\delta} = \sqrt{\varphi^{-1}}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/GoldenHorizonMatching.golden_horizon_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive frequencies with omega strictly below delta, sigma is the positive contraction ratio omega/delta. The theorem constructs the single-entry real Hankel matrix and uses its canonical frozen effective index.

The rapidity is artanh(sigma), with the standard real Bogoliubov coefficients cosh and sinh. The logarithmic divergence is the natural logarithm of the effective index.

All seven source conditions are public: six biconditionals connect the golden index value to the defect, squared contraction ratio, two coefficient magnitudes, logarithmic divergence, and frequency ratio.

## References

- Truth anchor: `D5/S3/Weil/Pick/GoldenHorizonMatching.golden_horizon_matching`
- Dependency: [D5/S3/Quantum/Bogoliubov/BogoliubovNormConservation](../../Quantum/Bogoliubov/BogoliubovNormConservation.md)
- Dependency: [D5/S3/Weil/Pick/HorizonEffectiveIndex](HorizonEffectiveIndex.md)
