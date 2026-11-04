# Exact Isotropic Gaussian Binary Risk

## Abstract

The midpoint rule attains the exact equal-prior risk against every measurable randomized rule for two isotropic Gaussian laws.

**Definition 1.1 (Affine Gaussian law).**

$$\forall V: Type, [\operatorname{NormedAddCommGroup}(V)] [\operatorname{InnerProductSpace}(\mathbb{R}, V)] [\operatorname{FiniteDimensional}(\mathbb{R}, V)] [\operatorname{MeasurableSpace}(V)] [\operatorname{BorelSpace}(V)],\\{}\forall mu: V, \forall sigma: \mathbb{R}, \operatorname{law}(mu, sigma) = \operatorname{map}(\operatorname{stdGaussian}(V), \Lambda z: V, ((mu) + (((sigma) \cdot (z)))))$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.law` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law is the pushforward of the standard Gaussian by z mapped to mu plus sigma times z. The real noise scale in this definition is unrestricted; the optimum theorem assumes it is positive.

**Definition 1.2 (Equal-prior randomized risk).**

$$\forall V: Type, [\operatorname{NormedAddCommGroup}(V)] [\operatorname{InnerProductSpace}(\mathbb{R}, V)] [\operatorname{FiniteDimensional}(\mathbb{R}, V)] [\operatorname{MeasurableSpace}(V)] [\operatorname{BorelSpace}(V)],\\{}\forall muZero: V, \forall muOne: V, \forall sigma: \mathbb{R}, \forall q: V \to \mathbb{R}, \operatorname{risk}(muZero, muOne, sigma, q) = \frac{((\operatorname{integral}(\Lambda x: V, q\left(x\right), \operatorname{law}(muZero, sigma))) + (\operatorname{integral}(\Lambda x: V, ((1) - (q\left(x\right))), \operatorname{law}(muOne, sigma))))}{2}$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.risk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A rule q returns the probability of choosing label one. Its two class-conditional errors are the integrals of q under the first law and of one minus q under the second. The risk averages these two errors.

**Definition 1.3 (Standard Gaussian distribution function).**

$$\forall t: \mathbb{R}, \operatorname{phi}(t) = \operatorname{measureReal}(\operatorname{gaussianReal}(0, 1), \operatorname{Iic}(t))$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Phi is the real measure of the closed lower half-line under the standard one-dimensional Gaussian. The variance parameter is one.

**Definition 1.4 (Midpoint decision region).**

$$\forall V: Type, [\operatorname{NormedAddCommGroup}(V)] [\operatorname{InnerProductSpace}(\mathbb{R}, V)] [\operatorname{FiniteDimensional}(\mathbb{R}, V)] [\operatorname{MeasurableSpace}(V)] [\operatorname{BorelSpace}(V)],\\{}\forall muZero: V, \forall muOne: V, \operatorname{region}(muZero, muOne) = \operatorname{setOf}(\Lambda x: V, 0 \leq \operatorname{inner}(((muOne) - (muZero)), ((x) - (((\frac{1}{2}) \cdot ((((muZero) + (muOne)))))))))$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.region` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The region contains exactly the observations whose inner product with the mean difference, after centering at the midpoint of the means, is nonnegative. Ties choose label one.

**Definition 1.5 (Midpoint randomized rule).**

$$\forall V: Type, [\operatorname{NormedAddCommGroup}(V)] [\operatorname{InnerProductSpace}(\mathbb{R}, V)] [\operatorname{FiniteDimensional}(\mathbb{R}, V)] [\operatorname{MeasurableSpace}(V)] [\operatorname{BorelSpace}(V)],\\{}\forall muZero: V, \forall muOne: V, \operatorname{midpoint}(muZero, muOne) = \operatorname{indicator}(\operatorname{region}(muZero, muOne), \operatorname{constantOne}(V))$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.midpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The midpoint rule is the real-valued indicator of the midpoint region. It takes only zero and one, and is also an admissible randomized rule.

**Theorem 1.6 (Exact optimum over all measurable randomized rules).**

$$\forall V: Type, [\operatorname{NormedAddCommGroup}(V)] [\operatorname{InnerProductSpace}(\mathbb{R}, V)] [\operatorname{FiniteDimensional}(\mathbb{R}, V)] [\operatorname{MeasurableSpace}(V)] [\operatorname{BorelSpace}(V)],\\{}\forall muZero: V, \forall muOne: V, \forall sigma: \mathbb{R}, ((0 < sigma) \Rightarrow (((\operatorname{Measurable}(\operatorname{midpoint}(muZero, muOne))) \land (\forall x: V, ((0 \leq \operatorname{midpoint}(muZero, muOne)\left(x\right)) \land (\operatorname{midpoint}(muZero, muOne)\left(x\right) \leq 1))) \land (\operatorname{risk}(muZero, muOne, sigma, \operatorname{midpoint}(muZero, muOne)) = \operatorname{phi}(\frac{-\Vert ((muOne) - (muZero))\Vert }{((2) \cdot (sigma))})) \land (\forall q: V \to \mathbb{R}, ((\operatorname{Measurable}(q)) \Rightarrow (\forall x: V, ((0 \leq q\left(x\right)) \land (q\left(x\right) \leq 1))) \Rightarrow (\operatorname{phi}(\frac{-\Vert ((muOne) - (muZero))\Vert }{((2) \cdot (sigma))}) \leq \operatorname{risk}(muZero, muOne, sigma, q)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.isotropic_gaussian_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be any finite-dimensional real inner-product space with its Borel measurable structure. The means are arbitrary and sigma is positive. The theorem gives a measurable admissible midpoint rule, evaluates its risk as Phi of minus the mean separation divided by twice sigma, and bounds every measurable real-valued rule in the interval from zero to one by the same value. Every finite coordinate type is allowed, including the empty type.

In orthonormal coordinates, the isotropic covariance matrix has square root sigma times the identity. The multivariate Gaussian density formula therefore gives both laws a common positive finite normalization C and densities C times exp of minus the squared distance to the corresponding mean divided by twice sigma squared. The determinant expression makes C independent of the mean. The product of one-dimensional densities becomes this squared-norm exponential, and the orthonormal coordinate equivalence preserves volume. The empty coordinate product remains included.

The difference of the squared distances to the two means equals twice the inner product defining the midpoint region. Inside that region the first density is no greater, with equality on ties. The excess integrand of an arbitrary rule over the midpoint rule is then one minus q times the difference of the densities. Outside the region it is q times the opposite density difference. Both are nonnegative. Bounded measurable rules are integrable under the probability laws; changing measure with the actual densities and integrating this pointwise inequality gives the bound for every such rule.

For distinct means, projection of centered standard Gaussian noise Z onto their unit separation vector has standard Gaussian law, before the mean shift and noise scaling. The two midpoint error events become upper and strict lower half-lines at the corresponding half-separation thresholds. Gaussian reflection and the zero measure of a singleton evaluate both tails exactly. When the means coincide, the two risk integrands add to one and every admissible rule has risk one half. This also includes zero-dimensional spaces. The rule class here consists of measurable probability functions; a Markov-kernel formulation additionally requires its own risk-preserving correspondence.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.isotropic_gaussian_optimal`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.law`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.midpoint`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.phi`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.region`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.risk`
- Dependency: [D5/S3/Observer/Linear/GaussianObservationLaw](../../Observer/Linear/GaussianObservationLaw.md)
