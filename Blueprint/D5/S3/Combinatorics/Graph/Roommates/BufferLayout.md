# BufferLayout

## Abstract

Components consumed by the exact Mertens range-two probability theorem.

Declarations without a displayed formula retain explicit statement-projection gaps. Their descriptions state the model and proof roles; they do not claim a rendered formula for an unsupported projection.

**Theorem 1.1 (occupied_iff).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every request map into the six buffer sites that avoids the central sites 2 and 3, occupied (flags request) i is true exactly when some old request lands at i. The complete_requests proof uses this equivalence.

**Definition 1.2 (occupied).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deterministic layout covers every subset of the four boundary sites of a six-vertex buffer. Reserved sites stand for old requesters. The generic request-completion theorem handles any injective family of old requests avoiding the two central sites, produces an actual involution, and allows only central new singles. PaddedCompletion and CyclicClosure combine this local involution with the separate stability and global injectivity proofs.

**Definition 1.3 (mate).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.mate`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.mate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deterministic layout covers every subset of the four boundary sites of a six-vertex buffer. Reserved sites stand for old requesters. The generic request-completion theorem handles any injective family of old requests avoiding the two central sites, produces an actual involution, and allows only central new singles. PaddedCompletion and CyclicClosure combine this local involution with the separate stability and global injectivity proofs.

**Theorem 1.4 (buffer_completion).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.buffer_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.buffer_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The deterministic layout covers every subset of the four boundary sites of a six-vertex buffer. Reserved sites stand for old requesters. The generic request-completion theorem handles any injective family of old requests avoiding the two central sites, produces an actual involution, and allows only central new singles. PaddedCompletion and CyclicClosure combine this local involution with the separate stability and global injectivity proofs.

**Theorem 1.5 (complete_requests).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.complete_requests`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.complete_requests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The deterministic layout covers every subset of the four boundary sites of a six-vertex buffer. Reserved sites stand for old requesters. The generic request-completion theorem handles any injective family of old requests avoiding the two central sites, produces an actual involution, and allows only central new singles. PaddedCompletion and CyclicClosure combine this local involution with the separate stability and global injectivity proofs.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.buffer_completion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.complete_requests`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.mate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied_iff`
