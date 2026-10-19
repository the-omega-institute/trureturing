# Entropy differences as resolvent integrals

## Abstract

Zero-safe convergent resolvent and Laplace integrals for finite entropy differences.

Let I be finite and let p_i and x_i be nonnegative real numbers. Put a=Σ_i p_i x_i. No normalization of the weights is required for this identity. With normalized weights, its right side is the Jensen difference for u log u. The integral is a single absolutely integrable difference; its separate resolvent terms need not be integrable.

**Theorem 1.1 (The finite entropy resolvent identity).**

$$\operatorname{IntegrableOn}\left(\frac{a}{t + a} - \operatorname{sum}\left(\operatorname{p}\left(i\right) \cdot \frac{\operatorname{x}\left(i\right)}{t + \operatorname{x}\left(i\right)}\right), \operatorname{Ioi}\left(0\right)\right) \land \int_{t > 0} \frac{a}{t + a} - \operatorname{sum}\left(\operatorname{p}\left(i\right) \cdot \frac{\operatorname{x}\left(i\right)}{t + \operatorname{x}\left(i\right)}\right) \mathrm{d} t = \operatorname{sum}\left(\operatorname{p}\left(i\right) \cdot \operatorname{x}\left(i\right) \cdot \operatorname{log}\left(\operatorname{x}\left(i\right)\right)\right) - a \cdot \operatorname{log}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/LaplaceEntropy.entropy_jensen_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and x_i>0, integrate x_i(1/(t+a)−1/(t+x_i)) using UniformIntegrals.reciprocal_difference, with the order of the shifts reversed when necessary. If x_i=0, the entire summand is zero. Finite linearity gives the identity because Σ_i p_i x_i=a. If a=0, nonnegativity forces every p_i x_i=0 and both sides vanish. This proves a scalar resolvent identity; it does not assert a Gaussian representation of matrix subentropy.

**Theorem 1.2 (The finite entropy Laplace identity).**

$$\operatorname{IntegrableOn}\left(\frac{\operatorname{sum}\left(\operatorname{p}\left(i\right) \cdot \operatorname{exp}\left(\left(0 - t\right) \cdot \operatorname{x}\left(i\right)\right)\right) - \operatorname{exp}\left(\left(0 - t\right) \cdot a\right)}{t^{2}}, \operatorname{Ioi}\left(0\right)\right) \land \int_{t > 0} \frac{\operatorname{sum}\left(\operatorname{p}\left(i\right) \cdot \operatorname{exp}\left(\left(0 - t\right) \cdot \operatorname{x}\left(i\right)\right)\right) - \operatorname{exp}\left(\left(0 - t\right) \cdot a\right)}{t^{2}} \mathrm{d} t = \operatorname{sum}\left(\operatorname{p}\left(i\right) \cdot \operatorname{x}\left(i\right) \cdot \operatorname{log}\left(\operatorname{x}\left(i\right)\right)\right) - a \cdot \operatorname{log}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/LaplaceEntropy.entropy_jensen_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here the weights also satisfy Σ_i p_i=1. Put F(s)=Σ_i p_i exp(−s x_i)−exp(−s a). Finite convex-exponential Jensen gives F(s)≥0. The preceding resolvent integrand equals ∫_(s>0) t exp(−ts)F(s) ds. Its known integrability proves integrability of the nonnegative two-variable kernel. Fubini exchanges s and t, and the Gamma integral at order two gives ∫_(t>0)t exp(−ts)dt=1/s². This proves the Laplace identity without excluding zero x_i or imposing an unproved boundary-limit condition.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/LaplaceEntropy.entropy_jensen_laplace`
- Truth anchor: `D5/S3/Quantum/Subentropy/LaplaceEntropy.entropy_jensen_resolvent`
- Dependency: [D5/S3/Quantum/Subentropy/UniformIntegrals](UniformIntegrals.md)
