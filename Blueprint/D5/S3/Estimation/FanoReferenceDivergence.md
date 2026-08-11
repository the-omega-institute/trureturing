# Finite Fano with an Arbitrary Observation Reference

## Abstract

A positive normalized observation reference gives computable divergence forms of finite Fano, and the observation marginal attains the resulting family of bounds.

**Theorem 1.1 (Reference divergence upper-bounds mutual information).**

$$I(X; Y) \le D(p \Vert u \cdot m_{X})$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoReferenceDivergence.mutual_information_le_product_reference_divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This instance-level module is separate from the general counting module because it depends on the frozen instance-level DemonIdentity. SL-010 forbids the general artifact from importing that fact: generality is bounded above by the complete dependency closure. The general side's independently checked transitive closure contains fourteen modules, all general, and does not contain DemonIdentity. The two documents therefore record a dependency-layer split of material that began in one module.

Let X and Y be finite. Let p be a nonnegative mass function on Y x X with total mass one, and let u on the observation coordinate Y be strictly positive and normalized by sum_y u(y) = 1. With m_X denoting the hidden-coordinate marginal of p, the theorem states

$$
I(X; Y) \le D(p \Vert u \cdot m_{X})
$$

The frozen DemonIdentity already decomposes the reference divergence as

$$
D(p \Vert u \cdot m_{X})=I(X; Y)+ D(m_{Y} \Vert u)
$$

Discarding the marginal-to-reference term by Gibbs nonnegativity is the entire proof. The inequality is a one-line consequence of an already-frozen theorem, not a new inequality. Its value is that the reference u is free, so the resulting Fano floor can be computed from a joint-to-product-reference divergence without separately evaluating mutual information.

The inequality has a strictly stronger hypothesis than the identity from which it comes. The identity needs u only strictly positive. The inequality also needs u normalized, because Gibbs nonnegativity applies only when both arguments are genuine distributions. On a one-point space the unit mass compared with the positive constant reference two has the kernel-checked value

$$
D(1 \Vert 2)=-\log 2<0
$$

Numerically this is 1 times log(1/2), or -0.693147, so discarding that term would reverse the intended inequality. Strict positivity serves a different purpose: in the finite setting it supplies discrete absolute continuity for free.

**Theorem 1.2 (The observation marginal attains the reference bound).**

$$\exists u: Y \to \mathbb{R}, (\forall y, 0<u(y)) \land \sum_{y} u(y)=1 \land D(p \Vert u \cdot m_{X})=I(X; Y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoReferenceDivergence.exists_observation_marginal_reference_attaining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p again be a nonnegative normalized law on finite Y x X, and assume in addition that its observation marginal m_Y is strictly positive at every y. Then there exists a strictly positive normalized reference u whose product-reference divergence equals the mutual information. The witness is the observation marginal itself:

$$
u=m_{Y}, D(p \Vert u \cdot m_{X})=I(X; Y)
$$

For this choice the discarded term is the divergence of m_Y from itself and is zero, so the upper bound becomes equality. Exhibiting an attaining reference makes the arbitrary-reference family a genuine degree of freedom rather than an unavoidable loss. The support condition remains essential to the theorem as stated: if m_Y has a zero, the equality identity still holds, but this witness is not admissible in the strictly positive reference family.

**Theorem 1.3 (Reference divergence gives the finite Fano error floor).**

$$1-\frac{D(p \Vert u \cdot m_{X})+ \log 2}{\log \lvert X \rvert} \le P(g(Y)\neq X)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoReferenceDivergence.fano_error_probability_lower_bound_divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite, let p be a nonnegative normalized law on Y x X, let g from Y to X be arbitrary, and let u on Y be strictly positive and normalized. Assume card X is at least two and the hidden-coordinate marginal is the constant law 1/card X. Then the p-mass of pairs with g(y) unequal to x is at least

$$
1-\frac{D(p \Vert u \cdot m_{X})+ \log 2}{\log \lvert X \rvert} \le P(g(Y)\neq X)
$$

This is the uniform finite Fano floor with the mutual-information budget enlarged by the arbitrary-reference divergence bound. It constructs no estimator and places no restriction on g beyond its type.

**Theorem 1.4 (The reference-divergence product form bounds hypothesis count).**

$$(1-\varepsilon) \cdot \log \lvert X \rvert \le D(p \Vert u \cdot m_{X})+ \log 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoReferenceDivergence.fano_hypothesis_count_product_bound_divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite, let p be a nonnegative normalized law on Y x X, let g from Y to X be arbitrary, and let u on Y be strictly positive and normalized. Assume the hidden-coordinate marginal is uniform and the error mass is at most epsilon. With no cardinality restriction and no condition on epsilon, the theorem gives

$$
(1-\varepsilon) \cdot \log \lvert X \rvert \le D(p \Vert u \cdot m_{X})+ \log 2
$$

Like its mutual-information counterpart, this product form is primary because it remains valid when epsilon reaches or exceeds one and does not divide by 1 - epsilon.

**Theorem 1.5 (The reference-divergence quotient isolates the candidate budget).**

$$\log \lvert X \rvert \le \frac{D(p \Vert u \cdot m_{X})+ \log 2}{(1-\varepsilon)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoReferenceDivergence.fano_hypothesis_count_bound_divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same finite-space, probability-law, positive normalized reference, uniform hidden-marginal, arbitrary-estimator, and error-at-most-epsilon hypotheses as the divergence product theorem, add exactly epsilon < 1. Then

$$
\log \lvert X \rvert \le \frac{D(p \Vert u \cdot m_{X})+ \log 2}{(1-\varepsilon)}
$$

The sole additional condition makes 1 - epsilon positive, so dividing the side-condition-free product statement preserves the inequality. The normalization and strict-positivity assumptions on u remain in force; the quotient operation does not weaken either one.

## References

- Truth anchor: `D5/S3/Estimation/FanoReferenceDivergence.exists_observation_marginal_reference_attaining`
- Truth anchor: `D5/S3/Estimation/FanoReferenceDivergence.fano_error_probability_lower_bound_divergence`
- Truth anchor: `D5/S3/Estimation/FanoReferenceDivergence.fano_hypothesis_count_bound_divergence`
- Truth anchor: `D5/S3/Estimation/FanoReferenceDivergence.fano_hypothesis_count_product_bound_divergence`
- Truth anchor: `D5/S3/Estimation/FanoReferenceDivergence.mutual_information_le_product_reference_divergence`
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](../Divergence/GrandmotherTheorem.md)
- Dependency: [D5/S3/Entropy/Feedback/DemonIdentity](../Entropy/Feedback/DemonIdentity.md)
- Dependency: [D5/S3/Estimation/FanoDivergenceForm](FanoDivergenceForm.md)
