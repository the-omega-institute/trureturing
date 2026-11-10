# Exact North-Pole Ball Preservation

## Abstract

The exact unit-ball criterion for an axial affine map fixing the north pole gives the relaxation-time bound for positive exponential decay times.

**Theorem 1.1 (Sharp transverse criterion for the whole closed ball).**

$$\forall a\in \mathbb{R}, \forall \Lambda\in \mathbb{R}, (0 \leq a \land a \leq 1) \Rightarrow ((\forall x\in \mathbb{R}, \forall y\in \mathbb{R}, \forall z\in \mathbb{R}, (x)^2+(y)^2+(z)^2 \leq 1 \Rightarrow (\Lambda \cdot x)^2+(\Lambda \cdot y)^2+(az+1-a)^2 \leq 1) \iff (\Lambda)^2 \leq a)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ContractionGeometry/NorthPoleBallCriterion.north_pole_ball_preserving_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three real coordinates describe the closed Euclidean unit ball. Both transverse coordinates have the same real factor lambda, with either sign allowed. The axis drifts toward the fixed north pole. The Lean statement uses dampedAxis with gamma equal to one minus a; expanding that existing coordinate gives exactly a z plus one minus a. The criterion includes a equal to zero and a equal to one.

For sufficiency, the squared transverse radius is first multiplied by lambda squared, bounded by a, and then bounded using the input ball. The remaining axial defect is nonnegative:

$$
a \cdot (1-(z)^2)+(az+1-a)^2 = 1-a \cdot (1-a) \cdot (1-z)^2 \leq 1
$$

For necessity, suppose lambda squared exceeds a and choose the positive height deficit delta below. It is at most one. The sphere point has y equal to zero, z equal to one minus delta, and nonnegative x whose square is delta multiplied by (two minus delta).

$$
\Delta = \frac{(\Lambda)^2-a}{(\Lambda)^2+1}
$$

Its image has squared radius exceeding one by delta times the bracket below. Since delta multiplied by (lambda squared plus one) equals (lambda squared minus a), and a squared is nonnegative, the bracket is at least lambda squared minus a and is strictly positive. Thus a specific sphere point violates preservation whenever the criterion fails; no infinitesimal approximation is needed.

$$
\Delta \cdot (2((\Lambda)^2-a)-\Delta((\Lambda)^2-(a)^2)) > 0
$$

## Exponential relaxation in the same affine model

Assume positive real longitudinal time T one, transverse time T two, and observation time t. Set a and lambda to the following exponential factors, and assume that the very same map preserves the entire closed unit ball:

$$
a = e^{-\frac{t}{T_1}}, \Lambda = e^{-\frac{t}{T_2}}
$$

The axial factor lies strictly between zero and one. The criterion gives the following exact chain; injectivity and monotonicity of the real exponential and cancellation of positive time and denominators justify each step:

$$
e^{-\frac{2t}{T_2}} \leq e^{-\frac{t}{T_1}} \iff -\frac{2t}{T_2} \leq -\frac{t}{T_1} \iff T_2 \leq 2T_1
$$

At zero observation time both factors are one for every positive pair of time constants, so that time alone gives no rate inequality. At the zero-axial endpoint preservation forces lambda to be zero; at the unit-axial endpoint it permits precisely absolute lambda at most one. Pure amplitude damping has lambda squared equal to a and saturates the bound. This concerns a fixed north pole, a zero-temperature axial drift and an isotropic transverse factor. It does not extend that physical model to every environment or identify ball preservation with complete positivity.

## Additional dephasing requires a product envelope

If an additional nonnegative dephasing rate k is supplied together with the product-envelope assumption, exponential factors multiply as follows:

$$
e^{-\frac{t}{T_2}} = e^{-\frac{t}{2T_1}} \cdot e^{-kt}, k \geq 0
$$

At positive time this implies the reciprocal rate is one over twice T one plus k, hence the same relaxation bound. Rate addition depends on the assumed exponential individual envelopes and their product relation; geometric preservation alone does not supply that relation. For physical context see Krantz et al., A quantum engineer's guide to superconducting qubits, arXiv:1904.06560v3, equations 40–43 and the adjacent qualification on exponential individual decay functions.

## References

- Truth anchor: `D5/S3/QuantumChannels/ContractionGeometry/NorthPoleBallCriterion.north_pole_ball_preserving_iff`
- Dependency: [D5/S3/QuantumChannels/AmplitudeDampingContraction](../AmplitudeDampingContraction.md)
