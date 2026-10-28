# Absolute Discrepancy Series

## Abstract

Uniform quadratic marginal tails force the reciprocal square-root logarithmic profile of integer discrepancies to have an infinite sum almost everywhere.

**Definition 1.1 (Discrepancy profile).**

$$\forall x\in \mathbb{Z}, f(x)= \frac{1}{\sqrt{2+\lvert x\rvert} \operatorname{log}\left(2+\lvert x\rvert\right)}$$

*Formalization.* `D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.discrepancyProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integer absolute values are cast to the real numbers. The square-root and logarithm arguments are at least two, so every profile value is strictly positive and finite.

**Definition 1.2 (Shifted logarithmic weight).**

$$\forall j\in \mathbb{N}, w_{j}= \frac{1}{(j+1) \operatorname{log}\left(j+2\right)}$$

*Formalization.* `D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.shiftedLogWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index starts at zero. All arithmetic in the denominator is real arithmetic after casting the index.

**Theorem 1.3 (Divergence of the exact shifted weights).**

$$\sum_{j\in \mathbb{N}} \operatorname{ofReal}\left(w_{j}\right)= \infty$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.tsum_shiftedLogWeight_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each weight dominates the reciprocal of (j+2) log(j+2). Removing the first two terms of the inverse-logarithmic series preserves its divergence. Nonnegative extended-real summation records that divergence as infinity.

The inverse-logarithmic premise uses the Cauchy-condensation proof by Rémy Degenne in Wang2026Almost, distributed under Apache 2.0. The shifted comparison and its conversion to extended nonnegative summation give the weight used here.

**Theorem 1.4 (Exact lower envelope on the quadratic good event).**

$$\forall x\in \mathbb{Z}, \forall j\in \mathbb{N}, \forall C\in \mathbb{R}, 0\leq C \land \lvert x\rvert\leq C (j+1)^{2} \Rightarrow \frac{w_{j}}{\sqrt{C+2} (2+\frac{\operatorname{log}\left(C+2\right)}{\operatorname{log}\left(2\right)})}\leq f(x)$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.discrepancyProfile_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bound the profile argument by (C+2)(j+1) squared. Its square root is at most the product of the square root of C+2 and j+1. Its logarithm is at most log(C+2) plus twice log(j+1). Comparing log(j+1) and log(2) with log(j+2) gives the displayed denominator, with no discarded initial indices.

**Theorem 1.5 (Accumulation under uniform quadratic marginal tails).**

$$\forall S: Type, [\operatorname{MeasurableSpace}\left(S\right)], \forall \mu: \operatorname{Measure}\left(S\right), \forall E: \mathbb{N} \to S \to \mathbb{Z}, \operatorname{FiniteMeasure}\left(\mu\right) \land (\forall j\in \mathbb{N}, \operatorname{Measurable}\left(E_{j}\right)) \land (\forall \Delta\in \mathbb{R}, \Delta> 0 \Rightarrow \exists C\in \mathbb{R}, \forall j\in \mathbb{N}, \mu(\{a\in S\mid C (j+1)^{2}< \lvert E_{j}(a)\rvert\})\leq \operatorname{ofReal}\left(\Delta\right)) \Rightarrow \mu(\{a\in S\mid \sum_{j\in \mathbb{N}} \operatorname{ofReal}\left(f(E_{j}(a))\right)\neq \infty\})= 0$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.ae_tsum_discrepancyProfile_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All discrepancies are measurable integer-valued functions on one common finite measure space. For every positive real error a single finite real tail constant works for every index. The tail constant need not be nonnegative: replacing it by its maximum with zero enlarges the good event and permits the envelope estimate.

Use the reciprocal of the envelope denominator as a positive finite scale. The lower-quantile failure event is contained in the original quadratic-tail event. Apply the uniform lower-quantile series theorem to the exact shifted weights. Independence is never assumed.

The sum takes values in the nonnegative extended real numbers; ofReal embeds each positive real profile value. This conclusion expresses divergence of the ordinary nonnegative partial sums.

For an endpoint model, the common execution, its discrepancy variables, their marginal tail estimates and the occupied-shape lower bound must be established separately. This analytic implication alone identifies neither the endpoint law nor a conditional cycle hazard.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.ae_tsum_discrepancyProfile_eq_top`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.discrepancyProfile`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.discrepancyProfile_lower_bound`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.shiftedLogWeight`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.tsum_shiftedLogWeight_eq_top`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/UniformLowerQuantileSeries](UniformLowerQuantileSeries.md)
