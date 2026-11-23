# Common Spectral Perturbations on Intervals

## Abstract

Independent interval offsets give common weighted near-collision bounds.

Let J and K be countable. Frequencies g(j) have prescribed radii ε(j)>0. Each test k has finite support in J, nonnegative weights, a natural degree, a nonnegative closed resolution η(k), and a positive excess budget b(k). Write D(k) for the diagonal weight and E(k,h) for the weighted collision mass of h on that test's support.

For distinct degree vectors m and n, let L(m,n) be the maximum of |m(j)−n(j)| ε(j) over the support. The quantity A(k) sums the products of the weighted multinomial coefficients times min(1,η(k)/L(m,n)) over distinct ordered pairs. Write C for the sum of A(k)/b(k) in the extended nonnegative reals.

**Theorem 1.1 (One perturbation bounds every test's excess).**

$$C \le 1 \Rightarrow \left(\exists h \in J \to \mathbb{R},\; \left(\forall j \in J,\; \left|\operatorname{h}\left(j\right)-\operatorname{g}\left(j\right)\right| \le \varepsilon(j)\right) \land \left(\sum_{k \in K}\frac{\operatorname{E}\left(k, h\right)-\operatorname{D}\left(k\right)}{\operatorname{b}\left(k\right)} \le C \land \left(\forall k \in K,\; \operatorname{E}\left(k, h\right) \le \operatorname{D}\left(k\right) + \operatorname{b}\left(k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ContinuousSpectralPerturbations.exists_continuous_common_nearby_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a distinct pair choose a coordinate attaining L(m,n), which is positive. Fix all other offsets on the support. The closed collision condition is an affine band in the remaining coordinate, with length at most twice the resolution divided by the absolute slope. Intersecting with the perturbation interval and normalizing by its length gives the pairwise factor.

Finite marginals give the same distribution on the support of each test. Summing the weighted indicators gives A(k) as an upper bound on expected excess. The expected normalized sum is at most C. If it exceeded C at every allowed assignment, its integral would be strictly greater than C, since the radius constraint holds almost surely. At a selected assignment every summand is nonnegative and at most the total, which is at most one.

Positive radii give interval laws with nonzero length. Countability lets us impose all radius constraints almost surely and integrate the sum of test excesses. Nonnegative weights give nonnegative pair contributions. The nonnegative resolution includes the diagonal, and positive test budgets permit normalization. For two equal starting ordinates with unit radii and weights, a degree-one test at resolution two captures both ordered off-diagonal pairs for every allowed assignment. With excess budget one, C is two and the individual test fails. This computation uses direct arithmetic.

The result constructs a comparison spectrum. A prescribed counting law would also need estimates on threshold crossings, and the fixed zeta ordinates require arithmetic control of their own weighted near-collisions.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/ContinuousSpectralPerturbations.exists_continuous_common_nearby_bounds`
- Dependency: [D5/S3/Fourier/Concentration/FiniteSincCollisionMoment](FiniteSincCollisionMoment.md)
