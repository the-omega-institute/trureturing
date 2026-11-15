# Weighted posterior source normalization

## Abstract

Actual weighted posterior sources on the compact unit interval preserve the original complex L1 inputs and the exact extended closed-perspective cost.

Let X be any measurable space in any source universe and mu any measure. The real inputs p and q are measurable, integrable and nonnegative almost everywhere; neither strict positivity nor total-mass normalization is assumed. Replace them pointwise by P=max(p,0) and Q=max(q,0), set r=P+Q, and define theta=P/r in K=[0,1], with theta=0 when r=0. The actual definitions use Real.toNNReal. The weighted measure is eta=mu.withDensity(r), and nu is its measurable pushforward by theta. Zero source measure and the zero pair remain included.

**Theorem 1.1 (measurable_theta).**

$$\forall X : \operatorname{Type}\left(\right), (\forall mX : \operatorname{MeasurableSpace}\left(X\right), (\forall mu : \operatorname{Measure}\left(X\right), (\forall p : (X \to \mathbb{R}), (\forall q : (X \to \mathbb{R}), (\forall hpm : \operatorname{Measurable}\left(p\right), (\forall hqm : \operatorname{Measurable}\left(q\right), (\operatorname{Measurable}\left(\operatorname{theta}\left(p, q\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.measurable_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative finite representatives give a genuine K-valued measurable function, including exceptional null sets and zero fibers. The pointwise identities r theta=P and r(1-theta)=Q hold even when r=0.

**Theorem 1.2 (posteriorMeasure_eq_original).**

$$\forall X : \operatorname{Type}\left(\right), (\forall mX : \operatorname{MeasurableSpace}\left(X\right), (\forall mu : \operatorname{Measure}\left(X\right), (\forall p : (X \to \mathbb{R}), (\forall q : (X \to \mathbb{R}), (\forall hpn : \operatorname{AE}\left(mu, x \mapsto (0 \le p\left(x\right))\right), (\forall hqn : \operatorname{AE}\left(mu, x \mapsto (0 \le q\left(x\right))\right), (\operatorname{posteriorMeasure}\left(mu, p, q\right) = \operatorname{Map}\left(\operatorname{theta}\left(p, q\right), \operatorname{WithDensity}\left(mu, x \mapsto (\operatorname{ENNRealofReal}\left((p\left(x\right)) + (q\left(x\right))\right))\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.posteriorMeasure_eq_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonnegative representatives agree with the literal original inputs almost everywhere. Therefore nu is exactly theta_*((p+q)mu), with the real density embedded by ENNReal.ofReal. This is an equality of measures, not an assumed change-of-source field.

**Theorem 1.3 (posteriorMeasure_finite_regular).**

$$\forall X : \operatorname{Type}\left(\right), (\forall mX : \operatorname{MeasurableSpace}\left(X\right), (\forall mu : \operatorname{Measure}\left(X\right), (\forall p : (X \to \mathbb{R}), (\forall q : (X \to \mathbb{R}), (\forall hp : \operatorname{Integrable}\left(p, mu\right), (\forall hq : \operatorname{Integrable}\left(q, mu\right), ((\operatorname{IsFiniteMeasure}\left(\operatorname{posteriorMeasure}\left(mu, p, q\right)\right)) \land (\operatorname{Regular}\left(\operatorname{posteriorMeasure}\left(mu, p, q\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.posteriorMeasure_finite_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrability of the positive parts proves that the integral of r is finite. The withDensity measure is finite and its pushforward is finite. The Borel measure on the compact metric interval is regular by Mathlib's regularity theorem. The theorem itself only needs integrability; nonnegativity of the original inputs is needed to identify the original weighted source.

**Definition 1.4 (pullContinuous).**

$$\forall X : \operatorname{Type}\left(\right), (\forall mX : \operatorname{MeasurableSpace}\left(X\right), (\forall mu : \operatorname{Measure}\left(X\right), (\forall p : (X \to \mathbb{R}), (\forall q : (X \to \mathbb{R}), (\forall hpm : \operatorname{Measurable}\left(p\right), (\forall hqm : \operatorname{Measurable}\left(q\right), (\forall hp : \operatorname{Integrable}\left(p, mu\right), (\forall hq : \operatorname{Integrable}\left(q, mu\right), (\operatorname{HasType}\left(\operatorname{pullContinuous}\left(hpm, hqm, hp, hq\right), \operatorname{ContinuousComplexLinearMap}\left(\operatorname{ContinuousMap}\left(\operatorname{Icc}\left(0, 1\right), \operatorname{Complex}\left(\right)\right), \operatorname{ComplexLone}\left(X, mu\right)\right)\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.pullContinuous` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct the actual continuous complex-linear map by composing ContinuousMap.toLp, Lp.compMeasurePreserving with theta, and the already established PositiveTracePreservingL1Map.weightMap. The latter is scalar despite its historical namespace. No state-valued Radon-Nikodym density, matrix representation or continuity of an original preparation is used.

**Theorem 1.5 (pullContinuous_coe).**

$$\forall X : \operatorname{Type}\left(\right), (\forall mX : \operatorname{MeasurableSpace}\left(X\right), (\forall mu : \operatorname{Measure}\left(X\right), (\forall p : (X \to \mathbb{R}), (\forall q : (X \to \mathbb{R}), (\forall hpm : \operatorname{Measurable}\left(p\right), (\forall hqm : \operatorname{Measurable}\left(q\right), (\forall hp : \operatorname{Integrable}\left(p, mu\right), (\forall hq : \operatorname{Integrable}\left(q, mu\right), (\forall g : \operatorname{ContinuousMap}\left(\operatorname{Icc}\left(0, 1\right), \operatorname{Complex}\left(\right)\right), (\operatorname{EventuallyEq}\left(mu, \operatorname{pullContinuous}\left(hpm, hqm, hp, hq\right)\left(g\right), x \mapsto (\operatorname{SMul}\left(\operatorname{mass}\left(p, q, x\right), g\left(\operatorname{theta}\left(p, q\right)\left(x\right)\right)\right))\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.pullContinuous_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The a.e. value in the original complex L1 space is r(x)g(theta(x)). A weighted-measure exceptional set only transfers to mu away from r=0; the remaining fiber is handled by multiplication by zero. This supplies an actual original-domain input for every continuous complex g.

**Theorem 1.6 (pullContinuous_positive).**

$$\forall X : \operatorname{Type}\left(\right), (\forall mX : \operatorname{MeasurableSpace}\left(X\right), (\forall mu : \operatorname{Measure}\left(X\right), (\forall p : (X \to \mathbb{R}), (\forall q : (X \to \mathbb{R}), (\forall hpm : \operatorname{Measurable}\left(p\right), (\forall hqm : \operatorname{Measurable}\left(q\right), (\forall hp : \operatorname{Integrable}\left(p, mu\right), (\forall hq : \operatorname{Integrable}\left(q, mu\right), (\forall g : \operatorname{ContinuousMap}\left(\operatorname{Icc}\left(0, 1\right), \operatorname{Complex}\left(\right)\right), ((\forall t : \operatorname{Icc}\left(0, 1\right), (0 \le g\left(t\right))) \Rightarrow (\operatorname{AE}\left(mu, x \mapsto (0 \le \operatorname{pullContinuous}\left(hpm, hqm, hp, hq\right)\left(g, x\right))\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.pullContinuous_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise nonnegative continuous complex functions produce a.e. nonnegative original L1 inputs. Positivity uses the usual ComplexOrder cone.

**Theorem 1.7 (integral_pullContinuous).**

$$\forall X : \operatorname{Type}\left(\right), (\forall mX : \operatorname{MeasurableSpace}\left(X\right), (\forall mu : \operatorname{Measure}\left(X\right), (\forall p : (X \to \mathbb{R}), (\forall q : (X \to \mathbb{R}), (\forall hpm : \operatorname{Measurable}\left(p\right), (\forall hqm : \operatorname{Measurable}\left(q\right), (\forall hp : \operatorname{Integrable}\left(p, mu\right), (\forall hq : \operatorname{Integrable}\left(q, mu\right), (\forall g : \operatorname{ContinuousMap}\left(\operatorname{Icc}\left(0, 1\right), \operatorname{Complex}\left(\right)\right), (\operatorname{Integral}\left(g, \operatorname{posteriorMeasure}\left(mu, p, q\right)\right) = \operatorname{Integral}\left(\operatorname{pullContinuous}\left(hpm, hqm, hp, hq\right)\left(g\right), mu\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.integral_pullContinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex integral identity holds for every continuous g. It is the standard pushforward integral followed by the exact withDensity Bochner identity, and the L1 a.e. action above.

**Theorem 1.8 (pullContinuous_moments).**

$$\forall X : \operatorname{Type}\left(\right), (\forall mX : \operatorname{MeasurableSpace}\left(X\right), (\forall mu : \operatorname{Measure}\left(X\right), (\forall p : (X \to \mathbb{R}), (\forall q : (X \to \mathbb{R}), (\forall hpm : \operatorname{Measurable}\left(p\right), (\forall hqm : \operatorname{Measurable}\left(q\right), (\forall hp : \operatorname{Integrable}\left(p, mu\right), (\forall hq : \operatorname{Integrable}\left(q, mu\right), (\forall hpn : \operatorname{AE}\left(mu, x \mapsto (0 \le p\left(x\right))\right), (\forall hqn : \operatorname{AE}\left(mu, x \mapsto (0 \le q\left(x\right))\right), ((\operatorname{pullContinuous}\left(hpm, hqm, hp, hq\right)\left(1\right) = \operatorname{IntegrabletoLone}\left(\operatorname{IntegrableofReal}\left(\operatorname{Integrableadd}\left(hp, hq\right)\right), x \mapsto (\operatorname{ComplexofReal}\left(x \mapsto ((p\left(x\right)) + (q\left(x\right)))\left(x\right)\right))\right)) \land ((\operatorname{pullContinuous}\left(hpm, hqm, hp, hq\right)\left(coordinate\right) = \operatorname{IntegrabletoLone}\left(\operatorname{IntegrableofReal}\left(hp\right), x \mapsto (\operatorname{ComplexofReal}\left(p\left(x\right)\right))\right)) \land (\operatorname{pullContinuous}\left(hpm, hqm, hp, hq\right)\left((1) - (coordinate)\right) = \operatorname{IntegrabletoLone}\left(\operatorname{IntegrableofReal}\left(hq\right), x \mapsto (\operatorname{ComplexofReal}\left(q\left(x\right)\right))\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.pullContinuous_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

coordinate(t) is the complex embedding of t.val. These are exact equalities to the L1 classes of the original p+q, p and q, respectively. Thus composition with any original algebraic preparation on the entire complex L1 space preserves both prepared moments. No continuity premise or smaller preparation domain is introduced.

**Theorem 1.9 (closedPerspectiveCost_posterior).**

$$\forall X : \operatorname{Type}\left(\right), (\forall mX : \operatorname{MeasurableSpace}\left(X\right), (\forall mu : \operatorname{Measure}\left(X\right), (\forall p : (X \to \mathbb{R}), (\forall q : (X \to \mathbb{R}), (\forall hpm : \operatorname{Measurable}\left(p\right), (\forall hqm : \operatorname{Measurable}\left(q\right), (\forall hpn : \operatorname{AE}\left(mu, x \mapsto (0 \le p\left(x\right))\right), (\forall hqn : \operatorname{AE}\left(mu, x \mapsto (0 \le q\left(x\right))\right), (\forall f : (\mathbb{R} \to \mathbb{R}), (\forall hf : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\operatorname{closedPerspectiveCost}\left(hf, mu, p, q\right) = \operatorname{closedPerspectiveCost}\left(hf, \operatorname{posteriorMeasure}\left(mu, p, q\right), t \mapsto (\operatorname{Subtypeval}\left(t\right)), t \mapsto ((1) - (\operatorname{Subtypeval}\left(t\right)))\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.closedPerspectiveCost_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the literal closedPerspectiveCost from CurvaturePerspectiveEndpoints and the existing closedPerspectiveCost_withDensity. The pointwise weighted identities restore the original inputs. Push forward the real affine-support integral and the extended nonnegative curvature integral separately. The equality needs neither integrability nor finiteness of the source or cost; those are used elsewhere to obtain a finite regular posterior and the L1 map. Infinite zero/infinity endpoints, zero masses and the origin convention are retained without signed infinity cancellation.

This is the established weighted posterior construction, formalized as a consumed source-normalization supplier. The main reused ingredients are the project's exact homogeneous closed-perspective density-change theorem and scalar weightMap, and Mathlib's pushforward integration, Lp pullback, continuous-function Lp inclusion and finite Borel regularity APIs. It makes no novelty claim and does not establish arbitrary-von-Neumann reverse-test attainment, the chosen-predual identification, compactness of the normal-moment family, or the complete comparison of original source classes.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.closedPerspectiveCost_posterior`
- Truth anchor: `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.integral_pullContinuous`
- Truth anchor: `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.measurable_theta`
- Truth anchor: `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.posteriorMeasure_eq_original`
- Truth anchor: `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.posteriorMeasure_finite_regular`
- Truth anchor: `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.pullContinuous`
- Truth anchor: `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.pullContinuous_coe`
- Truth anchor: `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.pullContinuous_moments`
- Truth anchor: `D5/S3/Quantum/Divergence/PosteriorSourceNormalization.pullContinuous_positive`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation](MaximalHockeyStickL1Preparation.md)
