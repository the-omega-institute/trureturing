# Source Tree Representation

## Abstract

Free binary source trees have precisely the independently generated tagged HF codes.

**Theorem 1.1 (Every legal source code reconstructs a tree).**

Lean statement: `D5/S0/History/Spacetime/SourceTreeEncoding.sourceCode_full`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/SourceTreeEncoding.sourceCode_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction over the independent HF grammar reconstructs a FreeMagma Nat tree. Leaf and branch tags differ. Repeated natural leaves refer to the same source identifier, and event occurrence tags do not rename these leaves.

**Definition 1.2 (An exact representation).**

Lean statement: `D5/S0/History/Spacetime/SourceTreeEncoding.source_code_equiv`

*Formalization.* `D5/S0/History/Spacetime/SourceTreeEncoding.source_code_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The grammar reconstruction and injectivity proofs give both round trips. The carrier reuses Mathlib's free magma and the fixed HF pairing representation.

## References

- Truth anchor: `D5/S0/History/Spacetime/SourceTreeEncoding.sourceCode_full`
- Truth anchor: `D5/S0/History/Spacetime/SourceTreeEncoding.source_code_equiv`
- Dependency: [D5/S0/History/Spacetime/HFEncoding](HFEncoding.md)
