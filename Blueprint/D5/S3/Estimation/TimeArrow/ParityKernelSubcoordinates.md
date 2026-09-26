# Proper Coordinate Records of Parity Kernels

## Abstract

On the sign hypercube, every parity kernel started from the uniform law makes each proper set of coordinates an i.i.d. uniform record.

**Definition 1.1 (Parity character).**

$$\operatorname{chi}(x)= \prod_{j<d} x_{j}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates.parity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a sign vector x in the hypercube {-1, 1}^d, the parity chi(x) is the product of its coordinates, a real number equal to 1 or -1.

**Definition 1.2 (Parity kernel).**

$$P_{a}(x, y)= \frac{1+\operatorname{a}(x) \operatorname{chi}(y)}{2^{d}}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates.parityKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each real profile a on the hypercube defines the transition weights P_a(x, y). Every row sums to one because the parity sums to zero over the hypercube when d >= 1. The weights are nonnegative, hence a Markov kernel, exactly when |a| <= 1; the identities below hold for every real profile.

**Definition 1.3 (Coordinate-record law).**

$$\operatorname{L}(a, S, T, w)= \sum_{x_{0},...,x_{T}} \frac{1}{2^{d}} \prod_{t<T} P_{a}(x_{t}, x_{t+1}) \prod_{t\leq T} \mathbf{1}_{x_{t}|_{S}=w_{t}|_{S}}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates.subcoordinateLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a coordinate set S and prescribed sign vectors w_0, ..., w_T, the record weight is the total weight, under the uniform start and the kernel P_a, of the paths whose coordinates in S at every time t agree with those of w_t.

**Theorem 1.4 (Proper coordinate records are i.i.d. uniform).**

$$S \neq \{1,..., d\} \Rightarrow \operatorname{L}(a, S, T, w)= (\frac{1}{2^{\lvert S\rvert}})^{T+1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates.subcoordinateLaw_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every dimension d, every real profile a, every proper subset S of the coordinates, every horizon T and every record w, the record law equals (2^(-|S|))^(T+1). For |a| <= 1, when P_a is a Markov kernel, this says that the coordinates in S of the chain started from the uniform law form an independent sequence of uniform vectors on {-1, 1}^S. No condition on a is needed; the statement concerns only the proper coordinates.

On every fiber that fixes the coordinates of the proper set S the two parity classes have the same number of vertices, since the uniform laws of the two classes have equal proper marginals; hence the parity sums to zero on the fiber. A fiber has 2^(d - |S|) elements, so the kernel mass P_a(x, fiber) equals 2^(-|S|) from every start x. Summing out the last state of the path and inducting on T gives the product formula, with base case the uniform mass of one fiber.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates.parity`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates.parityKernel`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates.subcoordinateLaw`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates.subcoordinateLaw_eq`
- Dependency: [D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments](../../Analytic/ReflectedSpectrum/ParityConditionedMoments.md)
