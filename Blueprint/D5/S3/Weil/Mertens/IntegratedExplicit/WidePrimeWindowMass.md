# A uniform estimate in the right endpoint

## Abstract

Prime-tail mass on wide real intervals

**Theorem 1.1 (The logarithmic lower bound and divergence when RH fails).**

$$\forall b \in \mathbb{R},\; 1 < b \Rightarrow \left(\left(\left(\neg RH\right) \Rightarrow \left(\forall K \in \mathbb{R},\; \exists S \in \mathbb{R},\; \forall B \in \mathbb{R},\; S \le B \Rightarrow \left(\forall A \in \mathbb{R},\; 2 \le A \Rightarrow \left(A^{b} \le B \Rightarrow K \le \operatorname{N}\left(A, B\right) - 2 \cdot \operatorname{log}\left(\frac{B}{A}\right)\right)\right)\right)\right) \land \left(\exists C \in \mathbb{R},\; 0 \le C \land \left(\forall A \in \mathbb{R},\; \forall B \in \mathbb{R},\; 2 \le A \Rightarrow \left(A^{b} \le B \Rightarrow 2 \cdot \operatorname{log}\left(\frac{B}{A}\right) - C \le \operatorname{N}\left(A, B\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/WidePrimeWindowMass.prime_tail_wide_window_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let Qθ(x) be the integral of (θ(t)−t)/t² from x to infinity, where θ sums log p over primes p ≤ t. This is the tail in Zhao's equation (14), arXiv:2411.18903v2. Let N(A,B) be the integral of max(−Qθ(x),0)/√x from A to B.

Use the last whole power window inside [A,B], with Y = B^(1/b). Since A ≥ 2 and b > 1, the width condition gives A ≤ Y ≤ Y^b = B. The reference HasWindows interface in riemann-hypothesis asks for a whole power window in the relevant set above each prescribed threshold. Here the width condition gives a whole subinterval of each measured interval, and nonnegativity of the integrand transfers its mass lower bound to [A,B].

If RH fails, right-half-strip reduction gives a zero with real part β > 1/2. For any 0 < η < β−1/2, apply the pole estimate on [Y,Y^b] with loss b(β−1/2−η). This gives N(A,B) ≥ B^η above a threshold on B alone. Since log(B/A) ≤ log B and log B = o(B^η), the discrepancy diverges uniformly over admissible A.

Under RH the uniform bound on the absolute logarithmic remainder applies to every ordered pair in the domain. If RH fails, uniform divergence gives a nonnegative discrepancy above the cutoff for K = 0. Below that cutoff, nonnegative mass and monotonicity of the logarithm give a common lower bound for the discrepancy.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/WidePrimeWindowMass.prime_tail_wide_window_mass`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth](PrimeWindowPoleGrowth.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowMean](RHPrimeWindowMean.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../ZetaBridge/RightHalfStripRiemannReduction.md)
