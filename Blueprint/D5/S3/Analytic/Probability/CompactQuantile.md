# CompactQuantile

## Abstract

The generalized inverse of a real CDF pushes Lebesgue measure on the open unit interval to the original probability measure. Atoms and singular laws are included. The midpoint approximation uses bounded continuous real tests; integration against the quantile is stated for arbitrary normed real vector targets with the declared measurability assumption.

The construction of Daniel Lyng in Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f is adapted under Apache-2.0. Apache-2.0 license: docs/reports/licenses/econlib-strassen/LICENSE.txt. Strassen (1965) provides the historical martingale-transport context. In formulas, coe denotes the canonical coercion, dmu the integration measure, iUnion indexed union, smul scalar multiplication, and ae almost everywhere. Namespace-qualified Lean names and interval constructors retain their mathematical meaning; separated identifier words denote the corresponding underscored Lean constant.

**Definition 1.1 (quantile).**

$$\forall  (\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} ) (\operatorname{t} : \mathbb{R} ), \mu .\operatorname{quantile} \operatorname{t} = \operatorname{sInf} \{\operatorname{x} : \mathbb{R}  | \operatorname{t} \leq  (\mu  (\operatorname{Set}.\operatorname{Iic} \operatorname{x})).\operatorname{toReal}\}$$

*Formalization.* `D5/S3/Analytic/Probability/CompactQuantile.quantile` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The lower generalized inverse of the cumulative distribution function; the infimum convention defines it for every real probability level, while order and transport results use the open unit interval.

**Lemma 1.2 (set_nonempty).**

$$\forall  \{\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} \} [\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure} \mu ] \{\operatorname{t} : \mathbb{R} \}, \operatorname{t} < 1 \to  \{\operatorname{x} | \operatorname{t} \leq  (\mu  (\operatorname{Set}.\operatorname{Iic} \operatorname{x})).\operatorname{toReal}\}.\operatorname{Nonempty}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.set_nonempty` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

For every probability level below one, some finite right endpoint has cumulative mass at least that level.

**Lemma 1.3 (quantile_le_iff).**

$$\forall  \{\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} \} [\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure} \mu ] \{\operatorname{t} : \mathbb{R} \}, \operatorname{t} \in  \operatorname{Set}.\operatorname{Ioo} 0 1 \to  \forall  \{\operatorname{x} : \mathbb{R} \}, \mu .\operatorname{quantile} \operatorname{t} \leq  \operatorname{x} \iff  \operatorname{t} \leq  (\mu  (\operatorname{Set}.\operatorname{Iic} \operatorname{x})).\operatorname{toReal}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.quantile_le_iff` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Inside the open unit interval, the generalized inverse lies below x exactly when the cumulative mass at x reaches the requested probability level.

**Lemma 1.4 (monotoneOn_quantile).**

$$\forall  \{\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} \} [\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure} \mu ], \operatorname{MonotoneOn} \mu .\operatorname{quantile} (\operatorname{Set}.\operatorname{Ioo} 0 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.monotoneOn_quantile` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The generalized inverse is increasing on the open unit interval.

**Lemma 1.5 (aemeasurable_quantile_restrict_Ioo).**

$$\forall  \{\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} \} [\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure} \mu ], \operatorname{AEMeasurable} \mu .\operatorname{quantile} (\operatorname{MeasureTheory}.\operatorname{volume}.\operatorname{restrict} (\operatorname{Set}.\operatorname{Ioo} 0 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.aemeasurable_quantile_restrict_Ioo` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The generalized inverse is almost-everywhere measurable for Lebesgue measure restricted to the open unit interval.

**Theorem 1.6 (map_quantile_volume_Ioo).**

$$\forall  \{\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} \} [\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure} \mu ], \operatorname{MeasureTheory}.\operatorname{Measure}.\operatorname{map} \mu .\operatorname{quantile} (\operatorname{MeasureTheory}.\operatorname{volume}.\operatorname{restrict} (\operatorname{Set}.\operatorname{Ioo} 0 1)) = \mu $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.map_quantile_volume_Ioo` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Pushing Lebesgue probability on the open unit interval through the generalized inverse recovers the entire original law, including its atoms.

**Theorem 1.7 (integral_eq_integral_quantile).**

$$\forall  \{\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} \} [\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure} \mu ] \{\operatorname{E} : \operatorname{Type} \operatorname{u1}\} [\operatorname{NormedAddCommGroup} \operatorname{E}] [\operatorname{NormedSpace} \mathbb{R}  \operatorname{E}] (\varphi  : \mathbb{R}  \to  \operatorname{E}), \operatorname{MeasureTheory}.\operatorname{AEStronglyMeasurable} \varphi  \mu  \to  \int  (\operatorname{x} : \mathbb{R} ), \varphi  \operatorname{x} \operatorname{dmu} \mu  = \int  (\operatorname{t} : \mathbb{R} ) \operatorname{in} \operatorname{Set}.\operatorname{Ioo} 0 1, \varphi  (\mu .\operatorname{quantile} \operatorname{t})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.integral_eq_integral_quantile` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

An almost-everywhere strongly measurable function has the same Bochner integral under the original law as its composition with the quantile under unit-interval Lebesgue measure. The target is an arbitrary real normed vector space; no extra integrability premise is inserted.

**Definition 1.8 (binMidpoint).**

$$\forall  (\operatorname{n} : \mathbb{N} ) (\operatorname{t} : \mathbb{R} ), \operatorname{binMidpoint} \operatorname{n} \operatorname{t} = (\operatorname{Nat}.\operatorname{floor} (\operatorname{n} \cdot \operatorname{t}) + 1 / 2) / \operatorname{n}$$

*Formalization.* `D5/S3/Analytic/Probability/CompactQuantile.binMidpoint` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The midpoint of the uniform bin containing t, using the natural-number floor and real division. The definition is total even at n equal to zero.

**Lemma 1.9 (bins_pairwise_disjoint).**

$$\forall  (\operatorname{n} : \mathbb{N} ), \operatorname{Pairwise} (\operatorname{Function}.\operatorname{onFun} \operatorname{Disjoint} \operatorname{fun} (\operatorname{k} : \operatorname{Fin} \operatorname{n}) \mapsto  \operatorname{Set}.\operatorname{Ico} (\operatorname{coe} \operatorname{coe} \operatorname{k} / \operatorname{coe} \operatorname{n}) ((\operatorname{coe} \operatorname{coe} \operatorname{k} + 1) / \operatorname{coe} \operatorname{n}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.bins_pairwise_disjoint` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The n half-open equal bins indexed by Fin n are pairwise disjoint, including the empty family at n equal to zero.

**Lemma 1.10 (iUnion_bins_eq_Ico).**

$$\forall  (\operatorname{n} : \mathbb{N} ), 1 \leq  \operatorname{n} \to  \operatorname{iUnion}  (\operatorname{k} : \operatorname{Fin} \operatorname{n}), \operatorname{Set}.\operatorname{Ico} (\operatorname{coe} \operatorname{coe} \operatorname{k} / \operatorname{coe} \operatorname{n}) ((\operatorname{coe} \operatorname{coe} \operatorname{k} + 1) / \operatorname{coe} \operatorname{n}) = \operatorname{Set}.\operatorname{Ico} 0 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.iUnion_bins_eq_Ico` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

For every positive bin count, the union of the half-open equal bins is precisely the half-open unit interval.

**Definition 1.11 (stepFun).**

$$\forall  (\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} ) (\varphi  : \mathbb{R}  \to  \mathbb{R} ) (\operatorname{n} : \mathbb{N} ) (\operatorname{t} : \mathbb{R} ), \operatorname{stepFun} \mu  \varphi  \operatorname{n} \operatorname{t} = \varphi  (\mu .\operatorname{quantile} (\operatorname{binMidpoint} \operatorname{n} \operatorname{t}))$$

*Formalization.* `D5/S3/Analytic/Probability/CompactQuantile.stepFun` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Evaluate the test function at the quantile of the midpoint of the bin containing t.

**Lemma 1.12 (countable_not_continuousWithinAt_quantile).**

$$\forall  \{\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} \} [\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure} \mu ], \{\operatorname{t} | \operatorname{t} \in  \operatorname{Set}.\operatorname{Ioo} 0 1 \land  \neg \operatorname{ContinuousWithinAt} \mu .\operatorname{quantile} (\operatorname{Set}.\operatorname{Ioo} 0 1) \operatorname{t}\}.\operatorname{Countable}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.countable_not_continuousWithinAt_quantile` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The discontinuity set of the increasing generalized inverse within the open unit interval is countable.

**Theorem 1.13 (tendsto_integral_of_quantile_midpoint).**

$$\forall  \{\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} \} [\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure} \mu ] (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{Continuous} \varphi  \to  \forall  \{\operatorname{M} : \mathbb{R} \}, (\forall  (\operatorname{x} : \mathbb{R} ), |\varphi  \operatorname{x}| \leq  \operatorname{M}) \to  \operatorname{Filter}.\operatorname{Tendsto} (\operatorname{fun} (\operatorname{n} : \mathbb{N} ) \mapsto  1 / \operatorname{coe} (\operatorname{n} + 1) \cdot \sum  (\operatorname{k} : \operatorname{Fin} (\operatorname{n} + 1)), \varphi  (\mu .\operatorname{quantile} ((\operatorname{coe} \operatorname{coe} \operatorname{k} + 1 / 2) / (\operatorname{coe} \operatorname{n} + 1)))) \operatorname{Filter}.\operatorname{atTop} (\operatorname{nhds} (\int  (\operatorname{x} : \mathbb{R} ), \varphi  \operatorname{x} \operatorname{dmu} \mu ))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.tendsto_integral_of_quantile_midpoint` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

For a bounded continuous real test, equal-weight midpoint quantile sums converge to its expectation under the original law.

**Definition 1.14 (stopLoss).**

$$\forall  (\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} ) (\operatorname{z} : \mathbb{R} ), \mu .\operatorname{stopLoss} \operatorname{z} = \int  (\operatorname{x} : \mathbb{R} ), \operatorname{max} (\operatorname{x} - \operatorname{z}) 0 \operatorname{dmu} \mu $$

*Formalization.* `D5/S3/Analytic/Probability/CompactQuantile.stopLoss` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The expected positive part of the excess over a threshold, defined by the real Bochner integral.

**Lemma 1.15 (stopLoss_nonneg).**

$$\forall  \{\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} \} (\operatorname{z} : \mathbb{R} ), 0 \leq  \mu .\operatorname{stopLoss} \operatorname{z}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.stopLoss_nonneg` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Every stop-loss value is nonnegative; the assertion uses the total integral convention and needs no finiteness assumption.

**Lemma 1.16 (stopLoss_integrable).**

$$\forall  \{\mu  : \operatorname{MeasureTheory}.\operatorname{Measure} \mathbb{R} \} [\operatorname{MeasureTheory}.\operatorname{IsFiniteMeasure} \mu ], \operatorname{MeasureTheory}.\operatorname{Integrable} (\operatorname{fun} \operatorname{x} \mapsto  \operatorname{x}) \mu  \to  \forall  (\operatorname{z} : \mathbb{R} ), \operatorname{MeasureTheory}.\operatorname{Integrable} (\operatorname{fun} \operatorname{x} \mapsto  \operatorname{max} (\operatorname{x} - \operatorname{z}) 0) \mu $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/CompactQuantile.stopLoss_integrable` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

An integrable real coordinate under a finite measure makes every positive-part excess integrable.

## References

- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.aemeasurable_quantile_restrict_Ioo`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.binMidpoint`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.bins_pairwise_disjoint`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.countable_not_continuousWithinAt_quantile`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.iUnion_bins_eq_Ico`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.integral_eq_integral_quantile`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.map_quantile_volume_Ioo`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.monotoneOn_quantile`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.quantile`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.quantile_le_iff`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.set_nonempty`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.stepFun`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.stopLoss`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.stopLoss_integrable`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.stopLoss_nonneg`
- Truth anchor: `D5/S3/Analytic/Probability/CompactQuantile.tendsto_integral_of_quantile_midpoint`
