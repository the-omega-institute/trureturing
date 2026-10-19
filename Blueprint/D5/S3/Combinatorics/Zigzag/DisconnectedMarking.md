# Recovering Words from Actual Separation

## Abstract

An actual root-separating coloring determines a complete absolute successor word on every positive native path.

The marking table records colors of the actual signed endpoint roles. Live separated states force three-step blocks, while the dead states have neither a separated continuation nor a separated cap. The inverse uses actual endpoint colors; it does not assume six distinct roles at the antipode.

**Theorem 1.1 (The even native inverse).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedMarking.even_native_separation_code`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedMarking.even_native_separation_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r at least one and every positive native even path, a coloring that separates the roots and is equal on every actual selected edge yields an initial bit and successor word whose coded path is exactly the given path. The assertion recovers labels and all steps, including the even cap, without a separate charge assumption.

**Theorem 1.2 (The odd native inverse).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedMarking.odd_native_separation_code`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedMarking.odd_native_separation_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The odd counterpart forces the two final moves and singleton cap and recovers every original path label at the odd tail length.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedMarking.even_native_separation_code`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedMarking.odd_native_separation_code`
- Dependency: [D5/S3/Combinatorics/Zigzag/DisconnectedEncoding](DisconnectedEncoding.md)
