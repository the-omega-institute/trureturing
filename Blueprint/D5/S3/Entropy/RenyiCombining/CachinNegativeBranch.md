# Negative-Parameter Elasticity Certificate

## Abstract

A negative-parameter certificate makes the binary Renyi elasticity transform decrease.

Write n = alpha - 1. This module handles -1 < n < 0, corresponding to 0 < alpha < 1. It reuses the functions T, A, B and F and the real-power derivative identities of CachinElasticityMonotone. All powers use positive bases on (0,1).

**Theorem 1.1 (The elasticity transform is antitone for negative n).**

$$\forall {n: \mathbb{R}}, -1 < n \land n < 0 \implies \operatorname{AntitoneOn}\left(\operatorname{F}\left(n\right), \operatorname{Ioo}\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinNegativeBranch.antitoneOn_F_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reused four-term function J has J(1)=J'(1)=0 and J''(z)=n(n^2-1)z^(n-2)(1-z). On -1 < n < 0 this is nonnegative. Two applications of derivative monotonicity therefore give J >= 0, and the identity A'(r)=n r^(n-2)J(r^2)/(1-r^(2n))^2 gives A' <= 0. Here A > 0, -1 < B < 0 and B' > 0. Consequently F'=A'/(1+B)-(1+A)B'/(1+B)^2 is strictly negative. The resulting antitonicity is consumed by the convex clause of Hirche's Conjecture IV.18; it does not by itself state convexity in the entropy coordinate.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinNegativeBranch.antitoneOn_F_neg`
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone](CachinElasticityMonotone.md)
