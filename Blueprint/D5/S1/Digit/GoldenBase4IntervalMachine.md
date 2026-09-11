# Golden Base-Four Interval Machine

## Abstract

An explicit typed twenty-one-state table follows an exact golden-error invariant on every legal Fibonacci-weighted word.

**Definition 1.1 (An explicit typed twenty-one-state machine).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.machine`

*Formalization.* `D5/S1/Digit/GoldenBase4IntervalMachine.machine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The table uses the existing TypedPartialDFAO and its binary Zeckendorf base. All legal transitions are present; one after one remains undefined. The initial output and zero loop are both zero.

**Theorem 1.2 (Fibonacci input evaluation follows an exact recurrence).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.fibPair_append_digit`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.fibPair_append_digit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two coordinates evaluate the word with Nat.fib weights and its shifted weights. Appending a bit updates the registers to (v+a,q+v+2a). No canonical Zeckendorf encoder is redefined.

**Theorem 1.3 (The error coordinate intertwines arithmetic and transitions).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.error_append_digit`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.error_append_digit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial identity phi squared equals phi plus one converts the two-register update into e maps to (1-phi)e-a(1-phi) squared.

**Theorem 1.4 (Entire interval images fit the table).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.endpoint_certificate`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.endpoint_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each noninitial interval has a noninitial destination. Because the affine slope is negative, the image of the upper endpoint is compared with the destination lower endpoint. These are finite exact algebraic inequalities.

**Theorem 1.5 (The state invariant survives every defined transition).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.step_preserves_cell`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.step_preserves_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial singleton is handled separately. No premise about unreachable artificial cut points is needed: interval preservation and the initial invariant already imply that every reached error belongs to its state cell.

**Theorem 1.6 (A whole cell has one radix-four output).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.cell_output_strip`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.cell_output_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each cell lies in the half-open digit strip assigned to the output, inside an explicitly specified integer strip.

**Theorem 1.7 (The invariant determines two integer floors).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.cell_floor_values`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.cell_floor_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The interval bounds identify floor(e) and floor(4e) exactly, using the upstream integer floor interface.

**Theorem 1.8 (The represented integer has the emitted digit).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.cell_digit`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.cell_digit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting an integer coordinate does not change the digit. The theorem proves the difference of floors directly from inequalities rather than numerical approximation.

**Theorem 1.9 (The empty input starts at the zero singleton).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.initial_cell`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.initial_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial error and initial state satisfy the invariant.

**Theorem 1.10 (Induction transports the invariant through every successful run).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.runFrom_cell`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.runFrom_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This induction uses the existing runTransition semantics. It retains the full consumed prefix, relating each new state to the arithmetic value of the appended word.

**Theorem 1.11 (Every successful run computes the exact floor difference).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.successful_run_digit`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.successful_run_digit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement quantifies over words of arbitrary length. No finite regression extent or caller-supplied correctness implication occurs.

**Theorem 1.12 (Every permitted base step is implemented).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.legal_step_exists`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.legal_step_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite table is total on the allowed symbols of each numeration type.

**Theorem 1.13 (Every legal word has a successful run).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.legal_run_exists`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.legal_run_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction lifts legal base runs to machine runs. This closes the potential loophole in a theorem conditioned only on successful machine runs.

**Theorem 1.14 (All legal Fibonacci-weighted words receive the correct output).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.every_legal_word_correct`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.every_legal_word_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This combines totality on legal words with the invariant. The separate M01 dense-word legality and value bridge is not claimed here; powers-only minimality is also not claimed.

**Theorem 1.15 (Leading zeroes do not affect the output).**

Lean statement: `D5/S1/Digit/GoldenBase4IntervalMachine.leading_zero_invariant`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4IntervalMachine.leading_zero_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses the existing leading-zero theorem with the concrete zero self-loop.

## References

- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.cell_digit`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.cell_floor_values`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.cell_output_strip`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.endpoint_certificate`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.error_append_digit`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.every_legal_word_correct`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.fibPair_append_digit`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.initial_cell`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.leading_zero_invariant`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.legal_run_exists`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.legal_step_exists`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.machine`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.runFrom_cell`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.step_preserves_cell`
- Truth anchor: `D5/S1/Digit/GoldenBase4IntervalMachine.successful_run_digit`
- Dependency: [D5/S0/Automata/TypedPartialDFAOOverBase](../../S0/Automata/TypedPartialDFAOOverBase.md)
