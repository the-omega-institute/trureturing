# Individual colours and complementary-pair labels

## Abstract

Exact weighted fibres of the six-colour row-major scanner.

The three pair labels have colour fibres {0,5}, {1,4}, and {2,3}. The two scanner flags record actual earlier occurrences of colours one and two. A pair label retains both the allowed-colour multiplicity and the resulting flags.

**Definition 1.1 (Pair-label scanner transition).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.labelAdvance`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.labelAdvance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An allowed colour in pair one sets the first flag; an allowed colour in pair two sets the second flag. A forbidden colour contributes zero weight.

**Definition 1.2 (Multiplicity of one pair label).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.labelWeight`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.labelWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pair zero always has two lifts. Pair one has one lift before colour one appears and two afterwards. Pair two has no lift before colour one, one lift before colour two, and two lifts afterwards.

**Definition 1.3 (Scanning the entire pair row).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowFinish`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowFinish` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every cell is scanned, including the first cell that is absent from the next boundary.

**Definition 1.4 (The exact row multiplicity).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowWeight`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the successive single-cell weights using the evolving scanner flags.

**Theorem 1.5 (The exact weighted scanner sum).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.scanner_fibres`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.scanner_fibres` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word length, initial scanner state, and integer readout of final flags and the entire pair word, summing over allowed individual colour words equals the pair-word sum with these weights. Splitting off the first cell gives the induction; the six single-cell cases supply the exact fibres. This identity does not assume that either distinguished colour occurs.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.labelAdvance`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.labelWeight`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowFinish`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowWeight`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.scanner_fibres`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
