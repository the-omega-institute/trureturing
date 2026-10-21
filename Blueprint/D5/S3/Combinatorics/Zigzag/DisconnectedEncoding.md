# Absolute Successor Words

## Abstract

Initial bits and absolute successor words encode labelled zero-charge native paths in both parities.

False and true specify the two positive starting states. Each successor bit selects one of the four three-step blocks. Start charge, successive bit differences and final negative bit charge telescope to zero. The even cap and the odd final two steps with singleton are separate native constructions.

**Theorem 1.1 (Even labelled code recovery).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedEncoding.evenCodedChoice_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedEncoding.evenCodedChoice_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r at least one, equality of the native balanced coded choices implies equality of both the initial bit and the entire successor word. The starting label determines the bit, and native path recovery determines each word entry. No choice symmetry quotient is taken.

**Theorem 1.2 (Odd labelled code recovery).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedEncoding.oddCodedChoice_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedEncoding.oddCodedChoice_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The odd native decoder has the same code injection, at its own tail length and with its singleton cap retained.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedEncoding.evenCodedChoice_injective`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedEncoding.oddCodedChoice_injective`
- Dependency: [D5/S3/Combinatorics/Zigzag/ActiveSupport](ActiveSupport.md)
- Dependency: [D5/S3/Combinatorics/Zigzag/OddPaths](OddPaths.md)
