# A Variance Lower Bound for Weighted Near-Collisions

## Abstract

The variance bounds the amount of near-collision mass required at positive resolution.

Let J be a finite type with decidable equality and let g and w be real-valued functions on J. Write W for the total weight, μ for the mean frequency with weights w/W, and V for the weighted mean of (g−μ)² with those weights. The quantity E(p,η) is tailCollisionMass g w p η, counting all ordered pairs of degree-p frequency sums within distance η.

**Theorem 1.1 (A lower bound at finite frequency resolution).**

$$\forall j\in J, 0\leq\operatorname{w}\left(j\right)\quad\quad0<W, 0<p\in\mathbb{N}, 0<eta \Rightarrow \frac{9}{16} \cdot W^{2 \cdot p} \le (1 + \frac{4 \cdot \operatorname{sqrt}\left(p \cdot V\right)}{eta}) \cdot \operatorname{E}\left(p, eta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FiniteCollisionVariance.tailCollisionMass_lower_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Center the frequencies by subtracting μ. This shifts each degree-p frequency by the same amount pμ, so pair differences are preserved. The multinomial expansion of the p-th power of the weighted real exponential sum gives the same coefficients as the Fourier moment. At zero its value is Wᵖ. Differentiating twice at zero gives the centered second moment pVWᵖ because the first derivative of the single-frequency sum is zero there.

Chebyshev's inequality puts at least three quarters of the coefficient mass within distance 2√(pV) of zero. When V is zero, all positive weight lies at the center. Partition that closed interval into at most floor(4√(pV)/η)+1 bins of width η. Each same-bin ordered pair is a near-collision. Cauchy–Schwarz bounds the sum of squared bin weights below by the square of the total weight in the interval divided by the number of bins.

In the bounded-start certificate `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.exists_bounded_tail_window`, set η = 2/L and δ > 0. Its strict moment budget then requires (9/16) K N (W/δ)^(2p) < 1 + 2L√(pV), where K = 3+π²/3 and N is the number of time samples. The inequality constrains that certificate's averaging length. The arithmetic upper bound for E(p,2/L) and the earliest missing window are separate questions.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FiniteCollisionVariance.tailCollisionMass_lower_variance`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.exists_bounded_tail_window`
- Dependency: [D5/S3/Fourier/Concentration/FiniteSincCollisionMoment](FiniteSincCollisionMoment.md)
