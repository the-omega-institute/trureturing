# Symmetrizing the two noninitial complementary pairs

## Abstract

An exact first-appearance scanner identity with the correction for absent labels.

The existing scanner weights count individual-colour lifts of a word of complementary-pair labels. Exchanging labels one and two exchanges the two possible orders of their first appearance. Label zero is fixed.

**Definition 1.1 (Exchange of the two noninitial labels).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.swap`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.swap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The involution exchanges one and two and fixes zero.

**Definition 1.2 (A whole-word absence indicator).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.absent`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.absent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer indicator is one exactly when the specified label never occurs, including for the empty word.

**Theorem 1.3 (Exact scanner symmetrization).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word length and every pair-label word, four times the sum of its normalized scanner weight and that of the exchanged word equals the displayed power of two times the absence correction. The product term retains the all-zero case. The induction first establishes the one-seen-label identity, then splits on the first label. No colour-occurrence or surjectivity assumption is imposed. This pointwise identity does not by itself identify a graph count or settle A233178.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.absent`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.swap`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry](HardinA233255ShapeSymmetry.md)
