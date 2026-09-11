# Golden Base-Four Long-Tail Output

## Abstract

Long terminal zero tails have a state-independent arithmetic output. Independent tail channels therefore cannot strengthen the gap-only completion problem.

**Definition 1.1 (The alternating terminal digit).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroTailForgetting.longTailDigit`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroTailForgetting.longTailDigit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For tail length at least two, even lengths have digit three and odd lengths digit zero. The function is defined at all lengths, but the machine theorem retains the lower-length guard.

**Theorem 1.2 (Every transient reference state has the same long-tail output).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroTailForgetting.zero_tail_output`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ZeroTailForgetting.zero_tail_output` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two zero steps enter the negative core. Subsequent zero steps alternate between two finite cores. Induction uses the original run semantics and transition table, and covers every tail length.

**Theorem 1.3 (The terminal law agrees with the exact floor difference).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroTailForgetting.zero_tail_arithmetic_digit`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ZeroTailForgetting.zero_tail_arithmetic_digit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A successful prefix in the previous-one fiber may have arbitrary length. Appending at least two zeroes gives the parity digit under the original Fibonacci valuation, by the existing interval-machine arithmetic theorem.

**Theorem 1.4 (Free terminal channels carry no additional gap constraint).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroTailForgetting.free_tail_completion_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ZeroTailForgetting.free_tail_completion_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary trace, labels and fixed tail-zero/tail-one readouts, all longer parity labels can always be extended by constant readouts. Both directions are proved. This equivalence applies to independent readouts; it does not replace the common-map constraints imposed by an actual finite recurrent carrier.

## References

- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroTailForgetting.free_tail_completion_iff`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroTailForgetting.longTailDigit`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroTailForgetting.zero_tail_arithmetic_digit`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroTailForgetting.zero_tail_output`
- Dependency: [D5/S1/Digit/GoldenBase4IntervalMachine](GoldenBase4IntervalMachine.md)
