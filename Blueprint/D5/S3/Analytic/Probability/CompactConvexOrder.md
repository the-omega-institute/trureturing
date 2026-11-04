# CompactConvexOrder

## Abstract

Compact interval convex order includes both mass-one support conditions, equality of means, and all tests that are convex and continuous on the interval. No strict endpoint, absolute continuity, or finite-support condition is imposed. Stop-loss comparison gives the lower integrated-quantile inequalities used by conditional-mean discretization.

The construction of Daniel Lyng in Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f is adapted under Apache-2.0. Apache-2.0 license: docs/reports/licenses/econlib-strassen/LICENSE.txt. Strassen (1965) provides the historical martingale-transport context. In formulas, coe denotes the canonical coercion, dmu the integration measure, iUnion indexed union, smul scalar multiplication, and ae almost everywhere. Namespace-qualified Lean names and interval constructors retain their mathematical meaning; separated identifier words denote the corresponding underscored Lean constant.

**Definition 1.1 (ProbDist).**

$$\forall  (\alpha  : \operatorname{Type} \operatorname{u}) [\operatorname{MeasurableSpace} \alpha ], \operatorname{ProbDist} \alpha  = \operatorname{MeasureTheory}.\operatorname{ProbabilityMeasure} \alpha $$

*Formalization.* `D5/S3/Analytic/Probability/CompactConvexOrder.ProbDist` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The probability-law carrier is the native ProbabilityMeasure, with its original measurable structure.

**Definition 1.2 (expect).**

$$\forall  \{\alpha  : \operatorname{Type} \operatorname{u}\} [\operatorname{MeasurableSpace} \alpha ] (\operatorname{d} : \operatorname{ProbDist} \alpha ) (\operatorname{f} : \alpha  \to  \mathbb{R} ), \operatorname{d}.\operatorname{expect} \operatorname{f} = \int  (\operatorname{x} : \alpha ), \operatorname{f} \operatorname{x} \operatorname{dmu} \operatorname{d}.\operatorname{toMeasure}$$

*Formalization.* `D5/S3/Analytic/Probability/CompactConvexOrder.expect` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Expectation is the real integral against the measure underlying the probability law.

**Definition 1.3 (map).**

$$\forall  \{\alpha  : \operatorname{Type} \operatorname{u}\} \{\beta  : \operatorname{Type} \operatorname{v}\} [\operatorname{MeasurableSpace} \alpha ] [\operatorname{MeasurableSpace} \beta ] (\operatorname{d} : \operatorname{ProbDist} \alpha ) (\operatorname{f} : \alpha  \to  \beta ) (\operatorname{hf} : \operatorname{Measurable} \operatorname{f}), \operatorname{d}.\operatorname{map} \operatorname{f} \operatorname{hf} = \operatorname{MeasureTheory}.\operatorname{ProbabilityMeasure}.\operatorname{map} \operatorname{d} \operatorname{f}$$

*Formalization.* `D5/S3/Analytic/Probability/CompactConvexOrder.map` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

A measurable map transports the native probability law by pushforward.

**Lemma 1.4 (map_toMeasure).**

$$\forall  \{\alpha  : \operatorname{Type} \operatorname{u1}\} \{\beta  : \operatorname{Type} \operatorname{u2}\} [\operatorname{MeasurableSpace} \alpha ] [\operatorname{MeasurableSpace} \beta ] (\operatorname{d} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \alpha ) (\operatorname{f} : \alpha  \to  \beta ) (\operatorname{hf} : \operatorname{Measurable} \operatorname{f}), \operatorname{coe} (\operatorname{d}.\operatorname{map} \operatorname{f} \operatorname{hf}) = \operatorname{MeasureTheory}.\operatorname{Measure}.\operatorname{map} \operatorname{f} \operatorname{coe} \operatorname{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactConvexOrder.map_toMeasure` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The underlying measure of a transported probability law is the ordinary measure pushforward.

**Lemma 1.5 (expect_map).**

$$\forall  \{\alpha  : \operatorname{Type} \operatorname{u1}\} \{\beta  : \operatorname{Type} \operatorname{u2}\} [\operatorname{MeasurableSpace} \alpha ] [\operatorname{MeasurableSpace} \beta ] (\operatorname{d} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \alpha ) (\operatorname{f} : \alpha  \to  \beta ) (\operatorname{hf} : \operatorname{Measurable} \operatorname{f}) (\operatorname{g} : \beta  \to  \mathbb{R} ), \operatorname{MeasureTheory}.\operatorname{AEStronglyMeasurable} \operatorname{g} \operatorname{coe} (\operatorname{d}.\operatorname{map} \operatorname{f} \operatorname{hf}) \to  (\operatorname{d}.\operatorname{map} \operatorname{f} \operatorname{hf}).\operatorname{expect} \operatorname{g} = \operatorname{d}.\operatorname{expect} \operatorname{fun} \operatorname{x} \mapsto  \operatorname{g} (\operatorname{f} \operatorname{x})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactConvexOrder.expect_map` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Expectation after measurable pushforward equals expectation of the composed test, under the stated almost-everywhere strong measurability condition.

**Definition 1.6 (supportsOn).**

$$\forall  \{\alpha  : \operatorname{Type} \operatorname{u}\} [\operatorname{MeasurableSpace} \alpha ] (\operatorname{d} : \operatorname{ProbDist} \alpha ) (\operatorname{s} : \operatorname{Set} \alpha ), \operatorname{d}.\operatorname{supportsOn} \operatorname{s} \iff  \operatorname{d}.\operatorname{toMeasure} \operatorname{s} = 1$$

*Formalization.* `D5/S3/Analytic/Probability/CompactConvexOrder.supportsOn` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Support on a set means that the set has probability one; it does not mean that every point lies in a topological support.

**Lemma 1.7 (ae_mem_of_supportsOn).**

$$\forall  \{\operatorname{d} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\operatorname{s} : \operatorname{Set} \mathbb{R} \}, \operatorname{MeasurableSet} \operatorname{s} \to  \operatorname{d}.\operatorname{supportsOn} \operatorname{s} \to  \forall \operatorname{ae}  (\operatorname{x} : \mathbb{R} ) \operatorname{dmu} \operatorname{coe} \operatorname{d}, \operatorname{x} \in  \operatorname{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactConvexOrder.ae_mem_of_supportsOn` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Mass one on a measurable set implies membership in that set almost everywhere under the same law.

**Lemma 1.8 (integrable_of_supportsOn_Icc).**

$$\forall  \{\operatorname{d} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\operatorname{f} : \mathbb{R}  \to  \mathbb{R} \}, \operatorname{d}.\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \operatorname{ContinuousOn} \operatorname{f} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \operatorname{MeasureTheory}.\operatorname{Integrable} \operatorname{f} \operatorname{coe} \operatorname{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactConvexOrder.integrable_of_supportsOn_Icc` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

A test continuous on a closed compact interval is integrable under any probability law assigning that interval mass one.

**Lemma 1.9 (integrable_id_of_supportsOn_Icc).**

$$\forall  \{\operatorname{d} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\operatorname{a} \operatorname{b} : \mathbb{R} \}, \operatorname{d}.\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \operatorname{MeasureTheory}.\operatorname{Integrable} \operatorname{id} \operatorname{coe} \operatorname{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactConvexOrder.integrable_id_of_supportsOn_Icc` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Compact interval concentration makes the real coordinate integrable.

**Definition 1.10 (ConvexOrderOnIcc).**

$$\forall  (\operatorname{a} \operatorname{b} : \mathbb{R} ) (\mu  \nu  : \operatorname{ProbDist} \mathbb{R} ), \operatorname{ConvexOrderOnIcc} \operatorname{a} \operatorname{b} \mu  \nu  \iff  (\mu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \land  \nu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \land  \mu .\operatorname{expect} \operatorname{id} = \nu .\operatorname{expect} \operatorname{id} \land  \forall  (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{ConvexOn} \mathbb{R}  (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \varphi  \to  \operatorname{ContinuousOn} \varphi  (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \mu .\operatorname{expect} \varphi  \leq  \nu .\operatorname{expect} \varphi )$$

*Formalization.* `D5/S3/Analytic/Probability/CompactConvexOrder.ConvexOrderOnIcc` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Interval convex order records both mass-one conditions, equality of means, and comparison of every real test convex and continuous on that interval.

**Theorem 1.11 (lowerIntegratedQuantile_ge_of_convexOrderOnIcc).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \}, \operatorname{ConvexOrderOnIcc} \operatorname{a} \operatorname{b} \mu  \nu  \to  \forall  \{\operatorname{t} : \mathbb{R} \}, \operatorname{t} \in  \operatorname{Set}.\operatorname{Ioc} 0 1 \to  \int  (\operatorname{u} : \mathbb{R} ) \operatorname{in} \operatorname{Set}.\operatorname{Ioc} 0 \operatorname{t}, (\operatorname{coe} \nu ).\operatorname{quantile} \operatorname{u} \leq  \int  (\operatorname{u} : \mathbb{R} ) \operatorname{in} \operatorname{Set}.\operatorname{Ioc} 0 \operatorname{t}, (\operatorname{coe} \mu ).\operatorname{quantile} \operatorname{u}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactConvexOrder.lowerIntegratedQuantile_ge_of_convexOrderOnIcc` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Interval convex order reverses the inequality between lower integrated quantiles at every positive level at most one.

## References

- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.ConvexOrderOnIcc`
- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.ProbDist`
- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.ae_mem_of_supportsOn`
- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.expect`
- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.expect_map`
- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.integrable_id_of_supportsOn_Icc`
- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.integrable_of_supportsOn_Icc`
- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.lowerIntegratedQuantile_ge_of_convexOrderOnIcc`
- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.map`
- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.map_toMeasure`
- Truth anchor: `D5/S3/Analytic/Probability/CompactConvexOrder.supportsOn`
- Dependency: [D5/S3/Analytic/Convexity/FiniteMajorization](../Convexity/FiniteMajorization.md)
- Dependency: [D5/S3/Analytic/Probability/CompactQuantile](CompactQuantile.md)
