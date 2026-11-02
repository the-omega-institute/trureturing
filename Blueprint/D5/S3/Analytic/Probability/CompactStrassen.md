# CompactStrassen

## Abstract

For arbitrary real endpoints and Borel probability measures of mass one on their closed interval, equal means and every interval-convex interval-continuous test inequality are equivalent to a single joint probability measure with both exact pushforward marginals and native joint-almost-everywhere conditional expectation of the second coordinate given the first equal to the first. Atomic, singular, and singleton laws are included. Empty-interval support premises are impossible. Coordinate integrability follows from compact marginal support. The construction takes a compact weak limit of finite martingale couplings, preserves both marginals, extends continuous tests to every bounded Borel test, then applies native conditional-expectation uniqueness. The native conditional-expectation identity uses the tested martingale law and integrability on the same joint measure.

The construction of Daniel Lyng in Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f is adapted under Apache-2.0. Apache-2.0 license: docs/reports/licenses/econlib-strassen/LICENSE.txt. Strassen (1965) provides the historical martingale-transport context. In formulas, coe denotes the canonical coercion, dmu the integration measure, iUnion indexed union, smul scalar multiplication, and ae almost everywhere. Namespace-qualified Lean names and interval constructors retain their mathematical meaning; separated identifier words denote the corresponding underscored Lean constant.

**Lemma 1.1 (tested_martingale_of_weak_limit).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\operatorname{piSeq} : \mathbb{N}  \to  \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\} \{\operatorname{piInf} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\}, (\forall  (\operatorname{n} : \mathbb{N} ), \operatorname{coe} (\operatorname{piSeq} \operatorname{n}) (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b} \times \operatorname{set}  \operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) = 1) \to  \operatorname{coe} \operatorname{piInf} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b} \times \operatorname{set}  \operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) = 1 \to  (\forall  (\operatorname{n} : \mathbb{N} ) (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{Measurable} \varphi  \to  (\exists  \operatorname{M}, \forall  (\operatorname{x} : \mathbb{R} ), |\varphi  \operatorname{x}| \leq  \operatorname{M}) \to  \int  (\operatorname{p} : \mathbb{R}  \times  \mathbb{R} ), (\operatorname{p}.2 - \operatorname{p}.1) \cdot \varphi  \operatorname{p}.1 \operatorname{dmu} \operatorname{coe} (\operatorname{piSeq} \operatorname{n}) = 0) \to  \operatorname{Filter}.\operatorname{Tendsto} (\operatorname{fun} \operatorname{n} \mapsto  \operatorname{piSeq} \operatorname{n}) \operatorname{Filter}.\operatorname{atTop} (\operatorname{nhds} \operatorname{piInf}) \to  \forall  (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{Continuous} \varphi  \to  (\exists  \operatorname{M}, \forall  (\operatorname{x} : \mathbb{R} ), |\varphi  \operatorname{x}| \leq  \operatorname{M}) \to  \int  (\operatorname{p} : \mathbb{R}  \times  \mathbb{R} ), (\operatorname{p}.2 - \operatorname{p}.1) \cdot \varphi  \operatorname{p}.1 \operatorname{dmu} \operatorname{coe} \operatorname{piInf} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactStrassen.tested_martingale_of_weak_limit` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

On one compact square, weak convergence of tested martingale laws preserves the displacement identity for every bounded continuous test of the first coordinate.

**Lemma 1.2 (tested_martingale_measurable_of_continuous).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\pi  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\}, \operatorname{coe} \pi  (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b} \times \operatorname{set}  \operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) = 1 \to  \operatorname{MeasureTheory}.\operatorname{Integrable} (\operatorname{fun} \operatorname{p} \mapsto  \operatorname{p}.1) \operatorname{coe} \pi  \to  \operatorname{MeasureTheory}.\operatorname{Integrable} (\operatorname{fun} \operatorname{p} \mapsto  \operatorname{p}.2) \operatorname{coe} \pi  \to  (\forall  (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{Continuous} \varphi  \to  (\exists  \operatorname{M}, \forall  (\operatorname{x} : \mathbb{R} ), |\varphi  \operatorname{x}| \leq  \operatorname{M}) \to  \int  (\operatorname{p} : \mathbb{R}  \times  \mathbb{R} ), (\operatorname{p}.2 - \operatorname{p}.1) \cdot \varphi  \operatorname{p}.1 \operatorname{dmu} \operatorname{coe} \pi  = 0) \to  \forall  (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{Measurable} \varphi  \to  (\exists  \operatorname{M}, \forall  (\operatorname{x} : \mathbb{R} ), |\varphi  \operatorname{x}| \leq  \operatorname{M}) \to  \int  (\operatorname{p} : \mathbb{R}  \times  \mathbb{R} ), (\operatorname{p}.2 - \operatorname{p}.1) \cdot \varphi  \operatorname{p}.1 \operatorname{dmu} \operatorname{coe} \pi  = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactStrassen.tested_martingale_measurable_of_continuous` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

For a joint law supported on a compact square and with integrable coordinates, vanishing displacement against every bounded continuous first-coordinate test extends to every bounded measurable first-coordinate test.

**Theorem 1.3 (martingaleCoupling_of_weak_limit).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\operatorname{muSeq} \operatorname{nuSeq} : \mathbb{N}  \to  \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\operatorname{piSeq} : \mathbb{N}  \to  \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\} \{\operatorname{piInf} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\}, \mu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \nu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  (\forall  (\operatorname{n} : \mathbb{N} ), \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsMartingaleCoupling} (\operatorname{muSeq} \operatorname{n}) (\operatorname{nuSeq} \operatorname{n}) (\operatorname{piSeq} \operatorname{n})) \to  (\forall  (\operatorname{n} : \mathbb{N} ), \operatorname{coe} (\operatorname{piSeq} \operatorname{n}) (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b} \times \operatorname{set}  \operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) = 1) \to  \operatorname{coe} \operatorname{piInf} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b} \times \operatorname{set}  \operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) = 1 \to  \operatorname{Filter}.\operatorname{Tendsto} (\operatorname{fun} \operatorname{n} \mapsto  \operatorname{piSeq} \operatorname{n}) \operatorname{Filter}.\operatorname{atTop} (\operatorname{nhds} \operatorname{piInf}) \to  \operatorname{Filter}.\operatorname{Tendsto} (\operatorname{fun} \operatorname{n} \mapsto  \operatorname{muSeq} \operatorname{n}) \operatorname{Filter}.\operatorname{atTop} (\operatorname{nhds} \mu ) \to  \operatorname{Filter}.\operatorname{Tendsto} (\operatorname{fun} \operatorname{n} \mapsto  \operatorname{nuSeq} \operatorname{n}) \operatorname{Filter}.\operatorname{atTop} (\operatorname{nhds} \nu ) \to  \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsMartingaleCoupling} \mu  \nu  \operatorname{piInf}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactStrassen.martingaleCoupling_of_weak_limit` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

A weak limit on the common compact square of genuine tested martingale couplings is again a tested martingale coupling of the two limiting marginals.

**Theorem 1.4 (compact_convex_order_iff_martingale).**

$$\forall  (\operatorname{a} \operatorname{b} : \mathbb{R} ) (\mu  \nu  : \operatorname{MeasureTheory}.\operatorname{ProbabilityMeasure} \mathbb{R} ), \operatorname{coe} \mu  (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) = 1 \to  \operatorname{coe} \nu  (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) = 1 \to  ((\int  (\operatorname{x} : \mathbb{R} ), \operatorname{x} \operatorname{dmu} \operatorname{coe} \mu  = \int  (\operatorname{x} : \mathbb{R} ), \operatorname{x} \operatorname{dmu} \operatorname{coe} \nu  \land  \forall  (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{ConvexOn} \mathbb{R}  (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \varphi  \to  \operatorname{ContinuousOn} \varphi  (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \int  (\operatorname{x} : \mathbb{R} ), \varphi  \operatorname{x} \operatorname{dmu} \operatorname{coe} \mu  \leq  \int  (\operatorname{x} : \mathbb{R} ), \varphi  \operatorname{x} \operatorname{dmu} \operatorname{coe} \nu ) \iff  \exists  (\pi  : \operatorname{MeasureTheory}.\operatorname{ProbabilityMeasure} (\mathbb{R}  \times  \mathbb{R} )), \operatorname{MeasureTheory}.\operatorname{Measure}.\operatorname{map} \operatorname{Prod}.\operatorname{fst} \operatorname{coe} \pi  = \operatorname{coe} \mu  \land  \operatorname{MeasureTheory}.\operatorname{Measure}.\operatorname{map} \operatorname{Prod}.\operatorname{snd} \operatorname{coe} \pi  = \operatorname{coe} \nu  \land  (\operatorname{coe} \pi )[\operatorname{Prod}.\operatorname{snd} | \operatorname{MeasurableSpace}.\operatorname{comap} \operatorname{Prod}.\operatorname{fst} (\operatorname{borel} \mathbb{R} )] =\operatorname{ae} [\operatorname{coe} \pi ] \operatorname{Prod}.\operatorname{fst})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactStrassen.compact_convex_order_iff_martingale` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

For every pair of compactly concentrated Borel real laws, equal means and all interval-local convex continuous test inequalities are equivalent to existence of one native joint probability law with both exact pushforward marginals and the joint-a.e. conditional-expectation identity. No strict endpoint or regularity assumption on the laws is required.

## References

- Truth anchor: `D5/S3/Analytic/Probability/CompactStrassen.compact_convex_order_iff_martingale`
- Truth anchor: `D5/S3/Analytic/Probability/CompactStrassen.martingaleCoupling_of_weak_limit`
- Truth anchor: `D5/S3/Analytic/Probability/CompactStrassen.tested_martingale_measurable_of_continuous`
- Truth anchor: `D5/S3/Analytic/Probability/CompactStrassen.tested_martingale_of_weak_limit`
- Dependency: [D5/S3/Analytic/Probability/ConditionalMeanApproximation](ConditionalMeanApproximation.md)
- Dependency: [D5/S3/Analytic/Probability/FiniteMartingaleCoupling](FiniteMartingaleCoupling.md)
