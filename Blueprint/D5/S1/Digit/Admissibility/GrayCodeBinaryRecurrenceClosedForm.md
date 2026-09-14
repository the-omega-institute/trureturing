# A Gray-Code Closed Form for a Binary Recurrence

## Abstract

Yanev's Gray-code formula for the nonnegative half of the binary recurrence.

The recurrence is considered on the natural numbers with initial value zero. The integer-indexed negative half is the separate sequence A163618 and is not asserted here.

The correction is integral in each parity branch. Over the integers it equals (6n + 1 - (-1)^n)/4, and the Gray-code term is OEIS A003188. The function div denotes natural-number integer division.

**Definition 1.1 (The binary recurrence).**

$$a\left(0\right) = 0 \land (\left(\forall m \in Nat,\; a\left(2 \cdot m\right) = 2 \cdot a\left(m\right)\right) \land \left(\forall m \in Nat,\; a\left(2 \cdot m + 1\right) = 2 \cdot a\left(m\right) + if\left(Even\left(m\right), 3, 1\right)\right))$$

*Formalization.* `D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.a` (`✓ std3`).

*Citation.* Velin Yanev (2016). *OEIS A163617, a(2*n) = 2*a(n), a(2*n + 1) = 2*a(n) + 2 + (-1)^n, for all n in Z*. URL: <https://oeis.org/A163617>.

*Commentary.*

At an even index the previous value is doubled. At an odd index it is doubled and increased by three when the half-index is even, or by one when the half-index is odd.

**Definition 1.2 (Binary reflected Gray code).**

$$\forall n \in Nat,\; gray\left(n\right) = xor\left(n, div\left(n, 2\right)\right)$$

*Formalization.* `D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.gray` (`✓ std3`).

*Citation.* Velin Yanev (2016). *OEIS A163617, a(2*n) = 2*a(n), a(2*n + 1) = 2*a(n) + 2 + (-1)^n, for all n in Z*. URL: <https://oeis.org/A163617>.

*Commentary.*

The binary reflected Gray code is the binary exclusive OR of n and its integer half.

**Definition 1.3 (The parity correction).**

$$\forall n \in Nat,\; corr\left(n\right) = if\left(Even\left(n\right), div\left(3 \cdot n, 2\right), div\left(3 \cdot n + 1, 2\right)\right)$$

*Formalization.* `D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.corr` (`✓ std3`).

*Citation.* Velin Yanev (2016). *OEIS A163617, a(2*n) = 2*a(n), a(2*n + 1) = 2*a(n) + 2 + (-1)^n, for all n in Z*. URL: <https://oeis.org/A163617>.

*Commentary.*

The even branch is floor(3n/2), and the odd branch is floor((3n+1)/2). These branches equal (6n + 1 - (-1)^n)/4 over the integers.

**Theorem 1.4 (Yanev's formula).**

$$\forall n \in Nat,\; a\left(n\right) = gray\left(n\right) + corr\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.yanev_a163617` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a163617-gray-code-binary-recurrence-closed-form` (proved) by `D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.yanev_a163617`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a163617-gray-code-binary-recurrence-closed-form","declaration_gid":"D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.yanev_a163617","resolution_kind":"proved"} -->

*Citation.* Velin Yanev (2016). *OEIS A163617, a(2*n) = 2*a(n), a(2*n + 1) = 2*a(n) + 2 + (-1)^n, for all n in Z*. URL: <https://oeis.org/A163617>.

*Commentary.*

Binary induction carries the equality through both recurrence branches. The Gray-code shifts follow by separating the low bit, while the correction supplies the matching parity increment.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.a`
- Truth anchor: `D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.corr`
- Truth anchor: `D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.gray`
- Truth anchor: `D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.yanev_a163617`
