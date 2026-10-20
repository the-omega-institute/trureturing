# The Two Native Disconnected Counts

## Abstract

For every natural r at least one, each native disconnected-choice count is 4*(2^(r-1)-1).

The objects retain every original class and Form label. Balance is integer balance at nonzero residues. Connectivity is weak connectivity on the actual active endpoints of the selected edges. Reflection supplies a second labelled sector; it does not identify choices.

**Definition 1.1 (The exact word fiber).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.DisconnectedCode`

*Formalization.* `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.DisconnectedCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A code consists of an initial Boolean b and an absolute successor word w of length l. Only the word equal everywhere to b is removed. For positive length, the word equal everywhere to the opposite bit remains allowed.

**Definition 1.2 (Even native choices and both sectors).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.evenDisconnectedChoicesEquiv`

*Formalization.* `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.evenDisconnectedChoicesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r at least one, the subtype of Choices (2*r) satisfying Balanced and failure of ActiveConnected is equivalent to the disjoint sum of two copies of DisconnectedCode (r-1). The positive native decoder realizes the first copy, and its zero-charge reflection realizes the second. Actual edge separation recovers the word from any disconnected balanced choice. Native code injection and reflection injection give uniqueness. The equivalence carries both inverse identities on the literal subtypes, including the antipodal cap.

**Definition 1.3 (Odd native choices and the singleton cap).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.oddDisconnectedChoicesEquiv`

*Formalization.* `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.oddDisconnectedChoicesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r at least one, the subtype of Choices (2*r+1) satisfying Balanced and failure of ActiveConnected has the same two-sector code type. The odd native decoder and its inverse retain the singleton cap and every label. Reflection preserves support at the same vertices. Both inverse identities belong to the equivalence.

**Theorem 1.4 (The even all-r formula).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.disconnectedCount_even`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.disconnectedCount_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural r with 1 <= r, disconnectedCount (2*r) = 4*(2^(r-1)-1). The literal filtered finite set has the cardinality of the native disconnected subtype. Each initial bit excludes one word from a function type of cardinality 2^(r-1); two bits and two labelled sectors supply the factor four.

**Theorem 1.5 (The odd all-r formula).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.disconnectedCount_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.disconnectedCount_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural r with 1 <= r, disconnectedCount (2*r+1) = 4*(2^(r-1)-1). Cardinality is transported through the odd native equivalence. At r=1 the empty word equals the constant initial word for either bit, so both code fibers and both counts are zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.DisconnectedCode`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.disconnectedCount_even`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.disconnectedCount_odd`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.evenDisconnectedChoicesEquiv`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedCounts.oddDisconnectedChoicesEquiv`
- Dependency: [D5/S3/Combinatorics/Zigzag/DisconnectedMarking](DisconnectedMarking.md)
- Dependency: [D5/S3/Combinatorics/Zigzag/DisconnectedRealization](DisconnectedRealization.md)
- Dependency: [D5/S3/Combinatorics/Zigzag/DisconnectedReflection](DisconnectedReflection.md)
