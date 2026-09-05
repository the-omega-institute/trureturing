# Certified Trigonometric Envelopes and Phase Reduction

## Abstract

Reusable certified-numerics infrastructure for the L2b layer of the G-c certificate: sharp trigonometric envelopes, exact golden floors, phase reduction, and coordinatewise finite-sum bounds.

This is the L2b infrastructure layer preregistered in addendum thirty-four. It proves no numerical assertion about the candidate zero, and it makes no claim about the Riemann hypothesis.

**Theorem 1.1 (Sharp any-order cosine envelope).**

$$\forall x \in \mathbb{R}, n \in \mathbb{N},\; \left|x\right| \le 1 \Rightarrow \left|\operatorname{cos}\left(x\right) - \sum_{0 \leq k < n} \frac{(-1)^{k} \cdot x^{2 \cdot k}}{(2 \cdot k)!}\right| \le \frac{\left|x\right|^{2 \cdot n}}{(2 \cdot n)!}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.abs_cos_sub_partial_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order n and every real x with absolute value at most one, the cosine Taylor error is bounded by the absolute value of the next term. This is the sharp alternating-series remainder, obtained from coefficient antitonicity and Mathlib's alternating-series error theorem.

**Theorem 1.2 (Sharp any-order sine envelope).**

$$\forall x \in \mathbb{R}, n \in \mathbb{N},\; \left|x\right| \le 1 \Rightarrow \left|\operatorname{sin}\left(x\right) - \sum_{0 \leq k < n} \frac{(-1)^{k} \cdot x^{2 \cdot k + 1}}{(2 \cdot k + 1)!}\right| \le \frac{\left|x\right|^{2 \cdot n + 1}}{(2 \cdot n + 1)!}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.abs_sin_sub_partial_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The analogous bound holds at every order for sine. The proof first handles nonnegative x by the alternating series and then transports the result across the odd symmetry of sine.

**Theorem 1.3 (An enclosed phase has a unit residual representative).**

$$\forall theta \in \mathbb{R}, a \in \mathbb{R}, b \in \mathbb{R}, k \in \mathbb{Z},\; \left(a \le theta \land \left(theta \le b \land \left|a - k \cdot (2 \cdot \pi)\right| + b - a \le 1\right)\right) \Rightarrow \left(\exists r \in \mathbb{R},\; theta = r + k \cdot (2 \cdot \pi) \land \left(\left|r\right| \le 1 \land \left(\operatorname{cos}\left(theta\right) = \operatorname{cos}\left(r\right) \land \operatorname{sin}\left(theta\right) = \operatorname{sin}\left(r\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.exists_reduced_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If theta lies in the certified interval from a to b and the chosen integer multiple of two pi leaves the whole interval inside a unit residual window, then r = theta - 2 pi k has absolute value at most one. Integer periodicity gives exact cosine and sine identities. Rational endpoint certificates can discharge the interval premise using Mathlib's pinned decimal bounds for pi.

**Theorem 1.4 (Real-coordinate interval accumulation).**

$$\forall I \in Type, s \in \operatorname{Finset}\left(I\right), z \in I \to \mathbb{C}, lo \in I \to \mathbb{R}, hi \in I \to \mathbb{R},\; \left(\forall i \in s,\; lo\left(i\right) \le \operatorname{Re}\left(z\left(i\right)\right) \land \operatorname{Re}\left(z\left(i\right)\right) \le hi\left(i\right)\right) \Rightarrow \left(\sum_{i \in s} lo\left(i\right) \le \operatorname{Re}\left(\sum_{i \in s} z\left(i\right)\right) \land \operatorname{Re}\left(\sum_{i \in s} z\left(i\right)\right) \le \sum_{i \in s} hi\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.sum_re_le_of_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lower and upper bounds are accumulated term by term with Finset.sum_le_sum. No positivity assumption on the summands is needed, so mixed-sign certified sums are supported.

**Theorem 1.5 (Imaginary-coordinate interval accumulation).**

$$\forall I \in Type, s \in \operatorname{Finset}\left(I\right), z \in I \to \mathbb{C}, lo \in I \to \mathbb{R}, hi \in I \to \mathbb{R},\; \left(\forall i \in s,\; lo\left(i\right) \le \operatorname{Im}\left(z\left(i\right)\right) \land \operatorname{Im}\left(z\left(i\right)\right) \le hi\left(i\right)\right) \Rightarrow \left(\sum_{i \in s} lo\left(i\right) \le \operatorname{Im}\left(\sum_{i \in s} z\left(i\right)\right) \land \operatorname{Im}\left(\sum_{i \in s} z\left(i\right)\right) \le \sum_{i \in s} hi\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.sum_im_le_of_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same mixed-sign finite-sum enclosure is available independently in the imaginary coordinate.

**Theorem 1.6 (Coordinate bounds imply an additive complex norm bound).**

$$\forall z \in \mathbb{C}, a \in \mathbb{R}, b \in \mathbb{R},\; \left(\left|\operatorname{Re}\left(z\right)\right| \le a \land \left|\operatorname{Im}\left(z\right)\right| \le b\right) \Rightarrow \left\lVert z \right\rVert \le a + b$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.norm_le_of_re_im_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This named companion binds Mathlib's complex norm inequality to the coordinate intervals. Its directed consumer is the L2c theorem g60_center_norm_lt.

**Theorem 1.7 (The first sixty-one golden floors are exact).**

$$\begin{aligned}o5FloorTable = (1, 3, 4, 6, 8, 9, 11, 12, 14, 16, 17, 19, 21, 22, 24, 25, 27, 29, 30, 32, 33, 35, 37, 38, 40, 42, 43, 45, 46, 48, 50, 51, 53, 55, 56, 58, 59, 61, 63, 64, 66, 67, 69, 71, 72, 74, 76, 77, 79, 80, 82, 84, 85, 87, 88, 90, 92, 93, 95, 97, 98)\\\forall v \in \mathbb{N},\; v \le 60 \Rightarrow \left\lfloor\left(v + 1\right) \cdot \varphi\right\rfloor = \operatorname{o5FloorTable}\left(v\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.o5Beta_floor_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed table is exactly floor((v+1) phi) for every v from zero through sixty. Each of its sixty-one entries is proved from the rational enclosure 1.618033 < phi < 1.618034, itself derived from the defining square root of five.

**Theorem 1.8 (The golden exponent has its table-driven affine form).**

$$\forall v \in \mathbb{N},\; v \le 60 \Rightarrow \operatorname{o5Beta}\left(v\right) = \operatorname{o5FloorTable}\left(v\right) - 1 - v + v \cdot \varphi$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.o5Beta_eq_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the certified range, the exact floor table converts the frozen golden exponent into an affine expression. The proof connects to the independently frozen closed form through floor plus fractional part, so the table definition is not a tautological carrier.

## References

- Truth anchor: `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.abs_cos_sub_partial_le`
- Truth anchor: `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.abs_sin_sub_partial_le`
- Truth anchor: `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.exists_reduced_phase`
- Truth anchor: `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.norm_le_of_re_im_bounds`
- Truth anchor: `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.o5Beta_eq_affine`
- Truth anchor: `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.o5Beta_floor_table`
- Truth anchor: `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.sum_im_le_of_bounds`
- Truth anchor: `D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.sum_re_le_of_bounds`
