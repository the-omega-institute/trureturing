# Running-Sum Residue Zeros

## Abstract

A running-sum residue recurrence is a doubling in disguise, so it vanishes exactly when its modulus is a power of two.

Indices and values are natural numbers. The recurrence enters as a hypothesis on an arbitrary sequence rather than as a construction, so the results apply to any sequence satisfying it. Reduction is natural remainder, and the empty sum is zero, which makes the first term the start value reduced.

**Definition 1.1 (The recurrence).**

$$\forall n \in \mathbb{N},  \operatorname{b}\left(n + 1\right) = \left(i + \sum_{k \in \operatorname{range}\left(n\right)} \operatorname{b}\left(k + 1\right)\right) \bmod j$$

*Formalization.* `D5/S1/Recurrence/Parity/RatajczakDoublingZero.IsRunningSumResidue` (`✓ std3`).

*Citation.* OEIS Foundation Inc. (2025). *OEIS A378252*. URL: <https://oeis.org/A378252>.

*Commentary.*

Each term is the start value plus every earlier term, reduced. At index zero the range is empty, so the first term is the start value reduced.

**Theorem 1.2 (The accumulation is a doubling).**

$$\forall n \in \mathbb{N},  \operatorname{b}\left(n + 1\right) = {2}^{n} \cdot i \bmod j$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/RatajczakDoublingZero.residue_eq_two_pow_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A378252*. URL: <https://oeis.org/A378252>.

*Commentary.*

The partial sum advances by the previous term, and that term is the previous partial sum reduced. Reducing before adding therefore replaces the partial sum by the term itself, turning the step into a doubling. Induction then gives the start value scaled by a power of two.

**Theorem 1.3 (The vanishing criterion).**

$$\operatorname{Coprime}\left(i, j\right) \Rightarrow (\exists t \in \mathbb{N}, \operatorname{b}\left(t + 1\right) = 0) \iff (\exists m \in \mathbb{N}, j = {2}^{m})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/RatajczakDoublingZero.exists_zero_iff_modulus_pow_two` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a378252-running-sum-residue-zero` (proved) by `D5/S1/Recurrence/Parity/RatajczakDoublingZero.exists_zero_iff_modulus_pow_two`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a378252-running-sum-residue-zero","declaration_gid":"D5/S1/Recurrence/Parity/RatajczakDoublingZero.exists_zero_iff_modulus_pow_two","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A378252*. URL: <https://oeis.org/A378252>.

*Commentary.*

Vanishing says the modulus divides a power of two times the start value. Coprimality moves the entire power onto the modulus, and a divisor of a prime power is a power of that prime. Conversely a power-of-two modulus divides the term whose exponent matches. The start value is not required to exceed the modulus; neither direction uses that.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/RatajczakDoublingZero.IsRunningSumResidue`
- Truth anchor: `D5/S1/Recurrence/Parity/RatajczakDoublingZero.exists_zero_iff_modulus_pow_two`
- Truth anchor: `D5/S1/Recurrence/Parity/RatajczakDoublingZero.residue_eq_two_pow_mul`
