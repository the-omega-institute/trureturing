# Unbounded Arithmetic Error Weight Below Twenty-One States

## Abstract

An anchored typed machine below twenty-one states must disagree with the exact golden digit function on legal inputs of unbounded nonzero-digit count.

**Theorem 1.1 (High-weight collisions determine the reference state).**

Lean statement: `D5/S1/Digit/GoldenBase4UnboundedError.high_weight_collision`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4UnboundedError.high_weight_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above a fixed nonzero-digit threshold, agreement on all legal inputs and equality of candidate states imply equality of reference states. The proof uses typing and thirteen finite diagnostic suffixes. It does not assume agreement on unobserved words from agreement only on powers.

**Theorem 1.2 (Bounded-weight disagreement cannot reduce the anchored state count).**

Lean statement: `D5/S1/Digit/GoldenBase4UnboundedError.bounded_error_weight_requires_twenty_one`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4UnboundedError.bounded_error_weight_requires_twenty_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The word 00001 is a one-containing loop at reference state 18. Repeating it gives arbitrarily high-weight access to all twenty noninitial states. Finite separation forces twenty different candidate states. None can be the initial state, because that state is fixed by zero and none of the twenty core states is. An injection from Option (Fin 20) proves the count.

**Theorem 1.3 (Every smaller anchored machine has unbounded-weight disagreements).**

Lean statement: `D5/S1/Digit/GoldenBase4UnboundedError.small_machine_unbounded_error_weight`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4UnboundedError.small_machine_unbounded_error_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each bound on the number of ones there is a legal reference input above that bound on which the candidate differs or is undefined. The input is not required to be a power of four. This excludes one proposed certification route without asserting the powers-only minimum.

**Theorem 1.4 (The reference label is the exact arithmetic floor difference).**

Lean statement: `D5/S1/Digit/GoldenBase4UnboundedError.small_machine_unbounded_arithmetic_errors`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4UnboundedError.small_machine_unbounded_arithmetic_errors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing successful_run_digit theorem identifies the mismatched label with the exact floor difference at the input's Fibonacci value. No numerical oracle, external Diophantine assumption or analytic density result is used in this proof.

## References

- Truth anchor: `D5/S1/Digit/GoldenBase4UnboundedError.bounded_error_weight_requires_twenty_one`
- Truth anchor: `D5/S1/Digit/GoldenBase4UnboundedError.high_weight_collision`
- Truth anchor: `D5/S1/Digit/GoldenBase4UnboundedError.small_machine_unbounded_arithmetic_errors`
- Truth anchor: `D5/S1/Digit/GoldenBase4UnboundedError.small_machine_unbounded_error_weight`
- Dependency: [D5/S1/Digit/GoldenBase4IntervalMachine](GoldenBase4IntervalMachine.md)
