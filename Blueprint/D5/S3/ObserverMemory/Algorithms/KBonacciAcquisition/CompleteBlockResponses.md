# KBonacci Complete Block Responses

## Abstract

Exact finite-horizon legality response classes and their field-valued response matrix.

**Definition 1.1 (Totalized scanner execution).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.run`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original partial k-tail scanner is totalized by retaining an optional live tail; a rejected execution is represented by none and remains absorbing.

**Definition 1.2 (Legality response).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.response`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.response` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The response records exactly whether the totalized execution remains live after a literal bit word. It exposes success versus rejection without adding a clock or source model.

**Definition 1.3 (Bounded bit-response equivalence).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.BitEquivalent`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.BitEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two optional scanner states are equivalent at horizon h when every literal word of length at most h has the same legality response.

**Definition 1.4 (Literal concatenation of complete blocks).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.blockWord`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.blockWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A list of width-m blocks is flattened in chronological order into its actual Boolean word.

**Definition 1.5 (Bounded complete-block equivalence).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.BlockEquivalent`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.BlockEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two optional scanner states are equivalent when every list of at most H literal width-m blocks has the same endpoint legality response.

**Theorem 1.6 (Live response classes).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.live_response_classes`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.live_response_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For live tails, bounded legality responses agree exactly when the remaining-one coordinates truncated at h agree. The proof uses the actual scanner responses, including the all-one separating word; it does not claim a physical source realization.

**Theorem 1.7 (Complete blocks exactly encode the bounded bit horizon).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.complete_block_budget`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.complete_block_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary widths and horizons, the complete-block relation is equivalent to the bit relation at horizon H*m. Short words are zero-padded because the scanner's zero transition preserves its legality response.

**Definition 1.8 (Canonical live-class representative).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.representative`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.representative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each truncated remaining-one coordinate is represented by the corresponding live scanner tail, giving one canonical state for every possible live response class.

**Definition 1.9 (Finite dependent family of bounded tests).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.BitTest`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.BitTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A bit test stores a word length below h+1 together with its literal Boolean word.

**Definition 1.10 (Complete Boolean response row).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.row`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row of a totalized scanner state records its legality response on every bounded literal word, retaining all tests rather than selecting a probe family.

**Theorem 1.11 (Exact number of live Boolean rows).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.live_class_count`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.live_class_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The range of live response rows has cardinality min k (h+1). The representative family is injective and every live tail has one of those rows.

**Theorem 1.12 (Exact number of totalized response rows).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.total_class_count`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.total_class_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding the absorbing rejection state contributes one row disjoint from the live rows, so the total row count is min k (h+1)+1.

**Definition 1.13 (Field-valued response matrix).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.responseMatrix`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.responseMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Over any field, the Boolean response rows are interpreted as zero-one matrix entries with optional scanner states as rows and all bounded literal tests as columns.

**Theorem 1.14 (Response rank equals the live class count).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.bit_response_rank`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.bit_response_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every field, the response matrix has rank min k (h+1). A lower-triangular all-one-word minor supplies the lower bound, while the coordinate factorization supplies the upper bound. This is the formal response-matrix result; the wider physical Proposition 3.3 remains open where it requires an additional source-history or acquisition bridge.

These declarations concern the totalized forbidden-1^k legality observation of the actual scanner. They establish the finite-horizon response classes, complete-block budget conversion, and field-valued response rank. They do not by themselves identify an arbitrary physical source history, a probability law, or a minimal autonomous quotient.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.BitEquivalent`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.BitTest`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.BlockEquivalent`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.bit_response_rank`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.blockWord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.complete_block_budget`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.live_class_count`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.live_response_classes`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.representative`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.response`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.responseMatrix`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.row`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.run`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.total_class_count`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NarrowWindowCost](NarrowWindowCost.md)
