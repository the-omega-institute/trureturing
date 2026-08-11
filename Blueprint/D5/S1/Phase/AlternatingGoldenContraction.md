# Alternating Golden Contraction

## Abstract

Golden negative-axis steps alternate and contract toward the center minus one.

**Theorem 1.1 (Every alternating golden orbit tends to minus one).**

$$G(x)=-1-\frac{x+1}{\varphi^3},\quad \lim_{n\to\infty}G^{n}(x)=-1$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/AlternatingGoldenContraction.alternating_golden_contraction_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Center an affine real recurrence at minus one. Each step reverses the centered displacement and divides its magnitude by the cube of the golden ratio. For every real starting point, the iterated recurrence converges to minus one. The private closed-form lemma also records the alternating geometric displacement after every finite number of steps, so the limit is derived from the exact dynamics rather than assumed.

Pinned Mathlib supplies `Real.one_lt_goldenRatio` and `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`. A source search found no declaration for this affine golden iteration or its closed form, so the result is a new short proof assembled around the library's geometric-power limit rather than a thin wrapper. The approximate finite readings in the source atom motivate the claim but are not used as hypotheses or numerical certificates.

## References

- Truth anchor: `D5/S1/Phase/AlternatingGoldenContraction.alternating_golden_contraction_tendsto`
