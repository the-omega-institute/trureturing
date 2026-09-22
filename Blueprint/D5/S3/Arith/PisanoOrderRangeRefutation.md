# The Number of Zeros in a Period Is Not Confined to Two

## Abstract

A two-term recurrence modulo thirteen has three zeros in one period, so the conjectured range for the number of such zeros is wrong.

**Definition 1.1 (The order of a modulus).**

$$pisanoOrder(p, q) = \frac{matrixPeriod(p, q)}{entryPoint(p, q)}$$

*Formalization.* `D5/S3/Arith/PisanoOrderRangeRefutation.pisanoOrder` (`✓ std3`).

*Citation.* Brennan Benfield, Oliver Lippard (2025). *Connecting Zeros in Pisano Periods to Prime Factors of K-Fibonacci Numbers*. URL: <https://arxiv.org/abs/2407.20048v2>.

*Commentary.*

The source calls the number of zeros in one period of the recurrence the order of the modulus. Zeros of the sequence occur exactly at the multiples of the entry point, the least index at which the modulus divides a term, and the entry point divides the period because a period ends on a zero. So the multiples of the entry point below the period are counted by the quotient, and that quotient is the order.

**Definition 1.2 (The conjectured range).**

$$(claim) \Leftrightarrow (\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall m \in \mathrm{Nat},\; \forall q \in \mathrm{Units},\; ((1 < m) \land ((b \ne 1) \land ((b \ne -1) \land ((\left|a\right| = \left|b\right| + 1) \land (q = -b))))) \Rightarrow (pisanoOrder(a, q) \in \{0, 1, 2\}))$$

*Formalization.* `D5/S3/Arith/PisanoOrderRangeRefutation.claim` (`✓ std3`).

*Citation.* Brennan Benfield, Oliver Lippard (2025). *Connecting Zeros in Pisano Periods to Prime Factors of K-Fibonacci Numbers*. URL: <https://arxiv.org/abs/2407.20048v2>.

*Commentary.*

The source writes the sequence as starting at zero and one and continuing by the rule that each term is the first parameter times the previous term plus the second parameter times the one before that. For the case where the second parameter is neither one nor minus one and the absolute value of the first exceeds the absolute value of the second by one, it asserts that the order takes only the values zero, one and two. Here the parameters are carried in the form this repository uses, where the recurrence subtracts the second parameter, so the pair is the first parameter together with the negative of the second; and the second parameter is required to be invertible, which restricts the assertion to moduli for which the sequence is periodic from the start. Refuting the restricted assertion refutes the one as written.

**Theorem 1.3 (The range fails).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PisanoOrderRangeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/pisano-order-range-refutation` (refuted) by `D5/S3/Arith/PisanoOrderRangeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pisano-order-range-refutation","declaration_gid":"D5/S3/Arith/PisanoOrderRangeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Brennan Benfield, Oliver Lippard (2025). *Connecting Zeros in Pisano Periods to Prime Factors of K-Fibonacci Numbers*. URL: <https://arxiv.org/abs/2407.20048v2>.

*Commentary.*

Take the first parameter three and the second two, so the recurrence adds three times the previous term to twice the one before, and take the modulus thirteen. The terms are zero, one, three, eleven, zero, nine, one, eight, zero, three, nine, seven, and the pair of consecutive terms then returns to zero and one, so the period is twelve. The entry point is four, since the fourth term is thirty-nine and the first, second and third terms are one, three and eleven. Twelve divided by four is three, which is larger than two, while two is neither one nor minus one and three exceeds two by one, so the pair satisfies the hypothesis. The failure is not isolated: the same happens for the parameters seven and six at the modulus five and for four and three at the modulus five. What makes the order small in this region is that the characteristic polynomial has one or minus one among its roots, which happens when the second parameter is one more than the first, or one less than the first with the opposite sign; the hypothesis as written keeps only the second of these two shapes and so admits pairs whose roots are irrational.

## References

- Truth anchor: `D5/S3/Arith/PisanoOrderRangeRefutation.claim`
- Truth anchor: `D5/S3/Arith/PisanoOrderRangeRefutation.pisanoOrder`
- Truth anchor: `D5/S3/Arith/PisanoOrderRangeRefutation.result`
- Dependency: [D5/S1/Recurrence/LucasCompanion](../../S1/Recurrence/LucasCompanion.md)
- Dependency: [D5/S1/Recurrence/LucasEvenDescent](../../S1/Recurrence/LucasEvenDescent.md)
