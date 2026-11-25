# Pairwise Bounds for a Common Spectral Perturbation

## Abstract

Pairwise reach and Euclidean scale refine a common perturbation budget.

Let J and K be countable and let r(j)>0 be the permitted frequency radii. Test k uses a finite support, nonnegative weights, natural degree, nonnegative closed resolution η(k), and positive budget b(k). Write D(k) for the diagonal and E(k,h) for the weighted collision mass of spectrum h on the support.

For a distinct degree pair m,n put a(j)=m(j)−n(j), A=Σ|a(j)|r(j), M=max |a(j)|r(j), and S=Σ(a(j)r(j))². Its probability budget is zero when the absolute original frequency difference exceeds η(k)+A. Otherwise the budget is the minimum of one, η(k)/M, and exp(1/2)√(15π/2)η(k)/√S. Set C to the sum of these bounds times the products of multinomial weights divided by the positive test budgets. The pairs are ordered.

**Theorem 1.1 (One spectrum realizes the weighted pairwise bounds).**

$$C \le 1 \Rightarrow \left(\exists h \in J \to \mathbb{R},\; \left(\forall j \in J,\; \left|\operatorname{h}\left(j\right)-\operatorname{g}\left(j\right)\right| \le \operatorname{r}\left(j\right)\right) \land \left(\sum_{k \in K}\frac{\operatorname{E}\left(k, h\right)-\operatorname{D}\left(k\right)}{\operatorname{b}\left(k\right)} \le C \land \left(\forall k \in K,\; \operatorname{E}\left(k, h\right) \le \operatorname{D}\left(k\right) + \operatorname{b}\left(k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/LocalizedCollisionBudgets.exists_continuous_common_nearby_localized_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the product of the normalized uniform interval measures, the shift of the pair difference is Σa(j)x(j). Almost surely its modulus is at most A. This makes the pair event null in the strictly separated case. For the other pairs, a nonzero difference and positive radii give positive M and S. The one-coordinate and Euclidean estimates bound the same event in the same marginal.

Use the common perturbation theorem for these pair probabilities. Finite marginals integrate the weighted off-diagonal terms and one assignment satisfies all the normalized budgets. At the separation boundary the closed band can still be reached. The bound concerns perturbed comparison spectra. The arithmetic estimate for the fixed zeta ordinates remains open.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/LocalizedCollisionBudgets.exists_continuous_common_nearby_localized_bounds`
- Dependency: [D5/S3/Fourier/Concentration/UniformPerturbationEuclidean](UniformPerturbationEuclidean.md)
