# Weighted Near-Collisions under Finite Spectral Perturbations

## Abstract

Small finite perturbations can bound weighted near-collisions at positive resolution.

Let J be a finite type with decidable equality. The real functions g and w give frequencies and weights with total W. For degree p, the multinomial coefficient including weights is c(m), and D is the sum of c(m)² over degree-p vectors m. The quantity E(g',p,η) sums c(m)c(n) over ordered pairs whose g' frequency sums are at distance at most η. The positive perturbation radius is ε.

**Theorem 1.1 (One perturbation with a controlled off-diagonal mass).**

$$(\forall j \in J,\; 0 \le \operatorname{w}\left(j\right))\quad p\in \mathbb{N}, M\in \mathbb{N}, 0<\varepsilon, 0\leq eta \Rightarrow \left(\exists h \in J \to \mathbb{R},\; \left(\forall j \in J,\; \left|\operatorname{h}\left(j\right)-\operatorname{g}\left(j\right)\right| \le \varepsilon\right) \land \operatorname{E}\left(h, p, eta\right) \le D + \frac{\min(M + 2, 1 + \left\lfloor\frac{eta \cdot (M + 1)}{\varepsilon}\right\rfloor)}{M + 2} \cdot (W^{2 \cdot p}-D)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FiniteSpectralPerturbation.exists_nearby_collision_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose each offset from M+2 equally spaced points in [−ε, ε]. For two distinct degree-p vectors, one coordinate of their difference is a nonzero integer. Fix all offsets except that coordinate. The difference of the perturbed frequency sums is affine with slope magnitude at least 2ε/(M+1) in the remaining grid index.

If any indices qualify, the least and greatest differ by at most 2η divided by the slope magnitude. The integer count is at most 1+floor(η(M+1)/ε) and at most M+2. Averaging each indicator over the finite product gives the displayed factor. Diagonal pairs contribute D at every assignment. Since the total coefficient weight is Wᵖ, the other pairs have total weight W²ᵖ−D. A single assignment is at most the upper bound on the mean.

The weighted mass is the same one used in `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.tail_moment_comparison`. The perturbations are chosen for one finite spectrum, one degree and one resolution. Applying a bound to the fixed actual zeta ordinates requires an arithmetic estimate for those ordinates.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.tail_moment_comparison`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSpectralPerturbation.exists_nearby_collision_bound`
- Dependency: [D5/S3/Fourier/Concentration/FiniteSincCollisionMoment](FiniteSincCollisionMoment.md)
