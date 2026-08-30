# Reflected Growth Pair and Negative-Square Signed Determinant

## Abstract

A reflected exponential pair exchanges under time reversal, remains reciprocal, and leaves a negative-square signed determinant after first-order cancellation.

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

**Definition 1.4 (The reflection-pair signed determinant).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectionPairSignedDeterminant`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectionPairSignedDeterminant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed determinant is the product of the two reflected generator rates. The main theorem identifies it exactly with minus delta squared. It is kept distinct from the standard polynomial discriminant.

**Definition 1.5 (The branch-forgetting symmetric readout).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGrowthSum`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectedGrowthSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The symmetric readout adds the expanding and contracting branches. It forgets which branch is which and therefore becomes even in time.

**Theorem 1.6 (Reflection leaves a negative-square invariant).**

$$\forall delta: \mathbb{R}, t: \mathbb{R}, r: \mathbb{R}, \operatorname{swapPair}(\operatorname{reflectedGrowthPair}(delta, t)) = \operatorname{reflectedGrowthPair}(delta, -t) \land \operatorname{fst}(\operatorname{reflectedGrowthPair}(delta, t)) \cdot \operatorname{snd}(\operatorname{reflectedGrowthPair}(delta, t)) = 1 \land \operatorname{pairTrace}(\operatorname{reflectedGenerator}(delta)) = 0 \land \operatorname{reflectionPairSignedDeterminant}(delta) = -delta^{2} \land (r - delta)(r + delta) = r^{2} - delta^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflected_growth_pair_negative_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Time reversal exchanges the two exponential branches, while their pointwise product remains one. At generator level the trace is zero and the signed determinant is minus delta squared.

The same invariant appears as the constant term of the characteristic factorization (r minus delta)(r plus delta) equals r squared minus delta squared. This is a general scalar theorem and carries no completed-zeta or Riemann-hypothesis premise.

**Theorem 1.7 (The standard polynomial discriminant is positive).**

$$\forall delta: \mathbb{R}, 0^{2} - 4 \cdot 1 \cdot (-delta^{2}) = 4 \cdot delta^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflection_pair_polynomial_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the monic polynomial r squared minus delta squared, the standard quadratic discriminant is four delta squared. This theorem prevents the negative determinant from being renamed as the conventional polynomial discriminant.

**Theorem 1.8 (Positive time separates expansion from contraction).**

$$\forall delta: \mathbb{R}, t: \mathbb{R}, 0 < delta \land 0 < t \Rightarrow 1 < \operatorname{fst}(\operatorname{reflectedGrowthPair}(delta, t)) \land \operatorname{snd}(\operatorname{reflectedGrowthPair}(delta, t)) < 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflected_growth_pair_forward_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive delta and positive time, the first branch is strictly above one and the reflected branch is strictly below one. Reversing time exchanges these roles through the branch-swap theorem.

**Theorem 1.9 (The symmetric observer is even in time).**

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
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflection_pair_polynomial_discriminant`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.reflectionPairSignedDeterminant`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.swapPair`
