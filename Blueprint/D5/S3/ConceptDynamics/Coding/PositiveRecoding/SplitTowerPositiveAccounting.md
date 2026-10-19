# Count the signed corrections of every actual split tower

## Abstract

Count the signed corrections of every actual split tower.

TowerWord.forward traverses the bottom lift and then the remaining tower. TowerWord.backward reverses the traversal using opposite positive letters in reverse order. inCount and outCount count actual incoming and outgoing stages; their sum is Tower.length. Both constructed words have that same positive-letter count.

For every actual finite Tower F K, forward_literal gives time at minus inCount on the forward word, and backward_literal gives time at minus outCount on the backward word. terminalWord combines the actual left tower, finite terminal vertex-and-edge relabeling and reversed right tower. terminal_literal retains minus inCount(left) minus outCount(right); equal lengths alone do not identify that sum with k. terminal_letters uses both depth equalities in Terminal F H P k to obtain 2*k. The terminal homeomorphism and square are inputs; the constructed word and its corrections are outputs.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Definition 1.1 (forward).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.forward`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.forward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal traversal: first the bottom lift, then the remaining tower.

**Definition 1.2 (backward).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.backward`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.backward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reverse traversal uses opposite POSITIVE letters in reverse order. It never puts an inverse homeomorphism into the word syntax.

**Theorem 1.3 (forward_literal).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.forward_literal`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.forward_literal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

EVERY concrete finite tower has the constructed positive forward word.

**Theorem 1.4 (backward_literal).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.backward_literal`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.backward_literal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

EVERY concrete finite tower also has a positive inverse-traversal word.

**Definition 1.5 (terminalWord).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.terminalWord`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.terminalWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All endpoint types here are the actual finite terminal presentations. The terminal J is finite vertex-and-edge data, not a history-map leaf.

**Theorem 1.6 (terminal_literal).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.terminal_literal`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.terminal_literal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The general formula deliberately keeps BOTH actual counts. Equal lengths alone would not justify replacing their sum by k.

**Remark 1.7 (inCount).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.inCount`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.inCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count the incoming constructors in the actual tower. These are precisely the negative unit corrections in forward traversal.

**Remark 1.8 (outCount).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.outCount`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.outCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count the outgoing constructors in the actual tower. These control the negative unit corrections in reverse traversal.

**Remark 1.9 (counts_length).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.counts_length`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.counts_length` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every tower stage is incoming or outgoing, so the two counts sum to the tower length. This does not identify either individual count.

**Remark 1.10 (forward_letters).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.forward_letters`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.forward_letters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructed forward word contains one positive letter per tower stage. Relabels contribute no positive letters.

**Remark 1.11 (backward_letters).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.backward_letters`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.backward_letters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reverse traversal also contributes one opposite positive letter per stage. Reversing order changes no letter count.

**Remark 1.12 (terminal_letters).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.terminal_letters`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.terminal_letters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left and right depth equalities of the actual terminal give a total of twice k positive letters. This length formula is separate from the two signed correction counts.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.backward`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.backward_letters`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.backward_literal`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.counts_length`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.forward`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.forward_letters`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.forward_literal`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.inCount`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.outCount`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.terminalWord`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.terminal_letters`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting.terminal_literal`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord](TypedPositiveSplitWord.md)
