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

For every natural k and every word q from Fin k into Fin 3, write W(q)=rowWeight((false,false),q) and A(q,c)=absent(q,c). Then 4*(W(q)+W(swap composed with q))=2^k*(1+A(q,1)+A(q,2)+5*A(q,1)*A(q,2)). The product term retains the all-zero case. The induction first establishes 2*rowWeight((true,false),q)=2^k*(1+A(q,2)), then splits on the first label. No colour-occurrence or surjectivity assumption is imposed. This pointwise identity does not by itself identify a graph count or settle A233178.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.absent`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.swap`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry](HardinA233255ShapeSymmetry.md)
