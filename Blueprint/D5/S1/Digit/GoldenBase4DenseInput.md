# Canonical Input Transport for the Golden Base-Four Machine

## Abstract

The existing M01 dense input has its exact arithmetic value and a legal run, connecting the interval machine to every required base-four power digit.

**Theorem 1.1 (Occupied indices fit the existing display length).**

Lean statement: `D5/S1/Digit/GoldenBase4DenseInput.occupied_index_bounds`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4DenseInput.occupied_index_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Upstream canonicality gives indices at least two and a decreasing gap of at least two. The head index used by M01 bounds every occupied index.

**Theorem 1.2 (Dense displays have their standard weighted values).**

Lean statement: `D5/S1/Digit/GoldenBase4DenseInput.dense_fibonacci_value`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4DenseInput.dense_fibonacci_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction over display width relates the existing interval-machine value to a finite sum of Nat.fib weights. This lemma is valid for any bit family.

**Theorem 1.3 (The M01 input word evaluates exactly to its argument).**

Lean statement: `D5/S1/Digit/GoldenBase4DenseInput.zeckendorfMSDWord_value`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4DenseInput.zeckendorfMSDWord_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index shift i maps to i+2 is a finite bijection from the selected display positions to the upstream occupied indices. Their Fibonacci sum is n by decode_wdigits. Neither the encoder nor its mathematical value is assumed as an extra premise.

**Theorem 1.4 (Separated bits admit legal runs of the shared base).**

Lean statement: `D5/S1/Digit/GoldenBase4DenseInput.separated_bits_run`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4DenseInput.separated_bits_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A previous-one entry requires the next displayed bit to be zero. The guarded induction proves legality without silently resetting the previous-bit type.

**Theorem 1.5 (The M01 word is accepted by the existing Zeckendorf base).**

Lean statement: `D5/S1/Digit/GoldenBase4DenseInput.zeckendorfMSDWord_legal`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4DenseInput.zeckendorfMSDWord_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonconsecutive occupied Fibonacci indices yield separated dense bits. The shared two-type base therefore accepts every M01 word, including the one-zero display of zero.

**Theorem 1.6 (The explicit machine computes the original M01 digit on every power).**

Lean statement: `D5/S1/Digit/GoldenBase4DenseInput.base4PowerWord_correct`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4DenseInput.base4PowerWord_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proved dense-word value and legality feed the interval invariant. Exact cast and power identities identify its floor difference with base4DigitInt and its output with base4GoldenDigit.

**Theorem 1.7 (A twenty-one-state witness satisfies the exact power task).**

Lean statement: `D5/S1/Digit/GoldenBase4DenseInput.twenty_one_state_power_witness`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4DenseInput.twenty_one_state_power_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness uses Fin 21 and the original M01 power-word and digit functions, together with the zero self-loop and zero initial output. This theorem has no finite-sample or caller-supplied correctness premise. It states an upper construction, not a minimum-state lower bound.

## References

- Truth anchor: `D5/S1/Digit/GoldenBase4DenseInput.base4PowerWord_correct`
- Truth anchor: `D5/S1/Digit/GoldenBase4DenseInput.dense_fibonacci_value`
- Truth anchor: `D5/S1/Digit/GoldenBase4DenseInput.occupied_index_bounds`
- Truth anchor: `D5/S1/Digit/GoldenBase4DenseInput.separated_bits_run`
- Truth anchor: `D5/S1/Digit/GoldenBase4DenseInput.twenty_one_state_power_witness`
- Truth anchor: `D5/S1/Digit/GoldenBase4DenseInput.zeckendorfMSDWord_legal`
- Truth anchor: `D5/S1/Digit/GoldenBase4DenseInput.zeckendorfMSDWord_value`
- Dependency: [D5/S1/Digit/GoldenBase4AutomataOracle](GoldenBase4AutomataOracle.md)
- Dependency: [D5/S1/Digit/GoldenBase4IntervalMachine](GoldenBase4IntervalMachine.md)
