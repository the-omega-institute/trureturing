# Common Spectral Perturbations on Intervals

## Abstract

Independent interval offsets give common weighted near-collision bounds.

Let J and K be countable. Frequencies g(j) have prescribed radii ε(j)>0. Each test k has finite support in J, nonnegative weights, a natural degree, a nonnegative closed resolution η(k), and a positive excess budget b(k). Write D(k) for the diagonal weight and E(k,h) for the weighted collision mass of h on that test's support.

For distinct degree vectors m and n, let L(m,n) be the maximum of |m(j)−n(j)| ε(j) over the support. The quantity A(k) sums the products of the weighted multinomial coefficients times min(1,η(k)/L(m,n)) over distinct ordered pairs. The budget sum is taken in the extended nonnegative reals.

**Theorem 1.1 (One perturbation bounds every test's excess).**

$$\sum_{k \in K}\frac{\operatorname{A}\left(k\right)}{\operatorname{b}\left(k\right)} \le 1 \Rightarrow \left(\exists h \in J \to \mathbb{R},\; \left(\forall j \in J,\; \left|\operatorname{h}\left(j\right)-\operatorname{g}\left(j\right)\right| \le \varepsilon(j)\right) \land \left(\forall k \in K,\; \operatorname{E}\left(k, h\right) \le \operatorname{D}\left(k\right) + \operatorname{b}\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ContinuousSpectralPerturbations.exists_continuous_common_nearby_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a distinct pair choose a coordinate attaining L(m,n), which is positive. Fix all other offsets on the support. The closed collision condition is an affine band in the remaining coordinate, with length at most twice the resolution divided by the absolute slope. Intersecting with the perturbation interval and normalizing by its length gives the pairwise factor.

Finite marginals give the same distribution on the support of each test. Summing the weighted indicators gives A(k) as an upper bound on expected excess. The expected sum of the excesses divided by b(k) is at most one. An assignment violating any test has total normalized excess strictly above one. The product measure gives full measure to the simultaneous radius constraint, so there is an allowed assignment satisfying all tests.

The result constructs a comparison spectrum. A prescribed counting law would also need estimates on threshold crossings, and the fixed zeta ordinates require arithmetic control of their own weighted near-collisions.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/ContinuousSpectralPerturbations.exists_continuous_common_nearby_bounds`
- Dependency: [D5/S3/Fourier/Concentration/FiniteSincCollisionMoment](FiniteSincCollisionMoment.md)
