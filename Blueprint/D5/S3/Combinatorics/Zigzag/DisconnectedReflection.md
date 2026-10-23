# The Second Labelled Sector

## Abstract

Native path reflection preserves actual weak support and active connectivity at the same vertices in both parities.

Reflection reverses and permutes the selected directed edges. It preserves their weak equivalence closure and their active endpoint set at each actual residue. The antipodal pair and the odd singleton obey their separate edge identities. The two sectors remain distinct native choices.

**Theorem 1.1 (Even active connectivity).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedReflection.even_reflection_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedReflection.even_reflection_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible even parameter and every positive native path, the reflected decoded choice is ActiveConnected if and only if the original decoded choice is ActiveConnected. The support relation is transported on the same vertices.

**Theorem 1.2 (Odd active connectivity).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedReflection.odd_reflection_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedReflection.odd_reflection_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corresponding odd connectivity equivalence includes the singleton edge and preserves the original active-support predicate.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedReflection.even_reflection_connected`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedReflection.odd_reflection_connected`
- Dependency: [D5/S3/Combinatorics/Zigzag/DisconnectedSupport](DisconnectedSupport.md)
