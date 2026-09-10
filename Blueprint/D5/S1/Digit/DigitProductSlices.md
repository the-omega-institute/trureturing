# Digit-Product Slices over Digits 2, 3, and 6

## Abstract

Decimal numbers over digits 2, 3, and 6 with at most one digit 3 admit complete divisibility classifications.

For a natural number N, digitProduct is the product of its base-ten digits, AllDigitsIn236 says that every digit belongs to the set {2,3,6}, and countThree counts occurrences of the digit 3.

**Theorem 1.1 (The positive zero-3 slice consists exactly of 2 and 6).**

$$\begin{aligned}\forall N \in \mathbb{N},\\0 < N \land \operatorname{AllDigitsIn236}(N) \land \operatorname{countThree}(N) = 0 \implies \\(\operatorname{digitProduct}(N) \mid N \iff (N = 2 \lor N = 6)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitProductSlices.zero_three_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive natural number with only the permitted digits and no digit 3, divisibility by the digit product is equivalent to being 2 or 6. The positivity premise is essential because the base-ten digit list of zero is empty.

**Theorem 1.2 (The unique-3 slice consists exactly of 3, 36, and 2232).**

$$\begin{aligned}\forall N \in \mathbb{N},\\\operatorname{AllDigitsIn236}(N) \land \operatorname{countThree}(N) = 1 \implies \\(\operatorname{digitProduct}(N) \mid N \iff (N = 3 \lor N = 36 \lor N = 2232)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitProductSlices.one_three_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing the unique digit 3 shows that two to the power length minus one divides the digit product. At length at least five, this forces divisibility by 16.

A kernel-checked exhaustion of the 81 four-digit words over {2,3,6}, restricted to suffixes containing at most one digit 3, rules out divisibility by 16. The remaining lists of length at most four are exhausted in the kernel and leave exactly 3, 36, and 2232. No claim is made about numbers containing two or more digits 3.

## References

- Truth anchor: `D5/S1/Digit/DigitProductSlices.one_three_slice`
- Truth anchor: `D5/S1/Digit/DigitProductSlices.zero_three_slice`
