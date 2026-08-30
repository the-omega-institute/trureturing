# Reflected Growth Pair and Negative-Square Discriminant

## Abstract

A reflected exponential pair exchanges under time reversal, remains reciprocal, and leaves the negative-square discriminant after first-order cancellation.

**Definition 1.1 (The reflected exponential pair).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGrowthPair`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGrowthPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two coordinates are exp(delta times t) and exp minus delta times t. They retain branch orientation instead of immediately collapsing to a symmetric cosh readout.

**Definition 1.2 (The branch-exchange involution).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.swapPair`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.swapPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

swapPair exchanges the two coordinates. The Lean module separately proves that applying this exchange twice restores every pair.

**Definition 1.3 (The reflected generator rates).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGenerator`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generator is the ordered pair (delta, minus delta). Its first-order trace cancels while its determinant retains the second-order split.

**Definition 1.4 (The reflection-pair discriminant).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectionPairDiscriminant`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectionPairDiscriminant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The discriminant is the product of the two reflected generator rates. The main theorem identifies it exactly with minus delta squared.

**Definition 1.5 (The branch-forgetting symmetric readout).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGrowthSum`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGrowthSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The symmetric readout adds the expanding and contracting branches. It forgets which branch is which and therefore becomes even in time.

**Theorem 1.6 (Reflection leaves a negative-square invariant).**

$$\forall delta: \mathbb{R}, t: \mathbb{R}, r: \mathbb{R}, \operatorname{swapPair}(\operatorname{reflectedGrowthPair}(delta, t)) = \operatorname{reflectedGrowthPair}(delta, -t) \land \operatorname{fst}(\operatorname{reflectedGrowthPair}(delta, t)) \cdot \operatorname{snd}(\operatorname{reflectedGrowthPair}(delta, t)) = 1 \land \operatorname{pairTrace}(\operatorname{reflectedGenerator}(delta)) = 0 \land \operatorname{reflectionPairDiscriminant}(delta) = -delta^{2} \land (r - delta)(r + delta) = r^{2} - delta^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflected_growth_pair_negative_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Time reversal exchanges the two exponential branches, while their pointwise product remains one. At generator level the trace is zero and the determinant is minus delta squared.

The same invariant appears in the characteristic factorization (r minus delta)(r plus delta) equals r squared minus delta squared. This is a general scalar theorem and carries no completed-zeta or Riemann-hypothesis premise.

**Theorem 1.7 (Positive time separates expansion from contraction).**

$$\forall delta: \mathbb{R}, t: \mathbb{R}, 0 < delta \land 0 < t \Rightarrow 1 < \operatorname{fst}(\operatorname{reflectedGrowthPair}(delta, t)) \land \operatorname{snd}(\operatorname{reflectedGrowthPair}(delta, t)) < 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflected_growth_pair_forward_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive delta and positive time, the first branch is strictly above one and the reflected branch is strictly below one. Reversing time exchanges these roles through the branch-swap theorem.

**Theorem 1.8 (The symmetric observer is even in time).**

$$\forall delta: \mathbb{R}, t: \mathbb{R}, \operatorname{reflectedGrowthSum}(delta, -t) = \operatorname{reflectedGrowthSum}(delta, t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflected_growth_sum_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding the two branches removes their orientation label. The resulting readout has identical values at t and minus t, which explains why a branch-forgetting observer is first-order blind to the split.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGenerator`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGrowthPair`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGrowthSum`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflected_growth_pair_forward_orientation`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflected_growth_pair_negative_square`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflected_growth_sum_even`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectionPairDiscriminant`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.swapPair`
