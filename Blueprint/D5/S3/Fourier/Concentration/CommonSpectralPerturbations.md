# Common Spectral Perturbations for Finite-Resolution Tests

## Abstract

One frequency assignment can satisfy a family of weighted collision bounds.

Let J have decidable equality and let K index the tests. Each j in J has a frequency g(j), a positive radius ε(j) and M(j)+2 allowed offsets for a natural M(j). The offsets are indexed by Fin(M(j)+2). An index f(j) defines H(f,j) = g(j) + ε(j)(2f(j)/(M(j)+1) − 1). Each k in K uses a finite support J(k), nonnegative weights on that support, a natural degree p(k) and a nonnegative resolution η(k).

For test k, let E(k,h) be its weighted near-collision mass for the restriction of h to J(k). Write W(k) for the weight sum, D(k) for the diagonal mass and B(k) for the full off-diagonal weight W(k) raised to 2p(k), minus D(k). Choose b(k)>0 whenever B(k)>0. For tests with B(k)>0 and b(k)<1, take ρ(k) to be any upper bound on the fraction min(M(j)+2, 1+floor(η(k)(M(j)+1)/ε(j)))/(M(j)+2) for every j in J(k). The budget term A(k) equals ρ(k)/b(k) for those tests and is zero for tests with B(k)=0 or b(k)≥1.

**Theorem 1.1 (One grid choice for all tests).**

$$\left(\forall T \in \operatorname{Finset}(K),\; \sum_{k \in T}\operatorname{A}\left(k\right) \le 1\right) \Rightarrow \left(\exists h \in J \to \mathbb{R},\; \left(\forall j \in J,\; \left|\operatorname{h}\left(j\right)-\operatorname{g}\left(j\right)\right| \le \varepsilon(j)\right) \land \left((\exists f \in \prod_{j \in J}\operatorname{Fin}(\operatorname{M}\left(j\right) + 2),\; \forall j \in J,\; \operatorname{h}\left(j\right) = \operatorname{H}\left(f, j\right)) \land \left(\forall k \in K,\; \operatorname{E}\left(k, h\right) \le \operatorname{D}\left(k\right) + \operatorname{b}\left(k\right) \cdot \operatorname{B}\left(k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CommonSpectralPerturbations.exists_common_nearby_collision_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite subfamily and average over the grids of the union of their supports. Each restricted assignment occurs the same number of times. The affine fiber count on the support bounds the mean of the excess E(k,h)−D(k) by ρ(k)B(k). Every such excess is nonnegative and at most B(k), so tests with B(k)=0 or b(k)≥1 hold for every assignment.

For the tests charged to the budget, divide the excess by b(k)B(k). If every assignment violates a test, the sum of these normalized excesses exceeds one at every point of the finite product. Its mean is at most the total budget, which also gives the result at budget one. Each test defines a closed cylinder set in the compact product of finite discrete grids. The finite-intersection property gives one assignment for the whole family.

The positive radius gives nonzero grid spacing. The positive tolerance permits the normalization used in the bound at budget one. The nonnegative weights give nonnegative ordered-pair masses. A zero resolution includes the diagonal, and a negative resolution gives zero collision mass. The simultaneous conclusion concerns perturbations of comparison spectra. Preserving a prescribed counting law requires a separate estimate for the chosen radii. For the fixed actual zeta ordinates the collision estimates still require arithmetic input.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CommonSpectralPerturbations.exists_common_nearby_collision_bounds`
- Dependency: [D5/S3/Fourier/Concentration/FiniteSpectralPerturbation](FiniteSpectralPerturbation.md)
