# Actual Realization and Root Activity

## Abstract

Absolute successor words realize actual root-separating colorings, with root activity determined by the initial bit and the word entries.

At class j the signed endpoint formulas determine the root incidences of all six original forms. At the reflected class the Form II endpoints are (-(j-1),j). Nonroot role exclusion suffices at the even antipode, where the two fresh signed roles may coincide. The construction imposes no injectivity condition there.

**Theorem 1.1 (Even actual coloring).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.even_native_code_coloring`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.even_native_code_coloring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r at least one, every initial bit and every successor word, a Boolean coloring of the actual residues takes values true and false at the two roots and is equal at the endpoints of every selected edge. Radial bands realize each three-step block and the antipodal cap.

**Theorem 1.2 (Odd actual coloring).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.odd_native_code_coloring`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.odd_native_code_coloring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corresponding odd coloring checks the two final paired steps and the singleton edge, as well as every interior block and the starting edge.

**Theorem 1.3 (Even root incidence).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.even_code_root_activity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.even_code_root_activity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every root bit s, the actual root (if s then 1 else -1) is active exactly when b=s or some entry of w equals s. The induction peels three native steps over an arbitrary suffix with an explicit successor state. It includes the empty word and the even cap.

**Theorem 1.4 (Odd root incidence).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.odd_code_root_activity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.odd_code_root_activity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r at least one, every initial bit b, every successor word w of length r-1 and every root bit s, the root (if s then 1 else -1) is active in the actual odd coded choice exactly when b=s or some entry of w equals s.

**Theorem 1.5 (The even excluded word).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.even_code_disconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.even_code_disconnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual even coded choice fails ActiveConnected exactly when w differs from the word constantly equal to its initial bit. Both roots are then active and have different colors. If that word is constant at the initial bit, the opposite root is absent and actual rootedness gives connectivity.

**Theorem 1.6 (The odd excluded word).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.odd_code_disconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.odd_code_disconnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identical exact exclusion holds for the odd coded choice, using the odd coloring and incidence identities on the original active support.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.even_code_disconnected`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.even_code_root_activity`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.even_native_code_coloring`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.odd_code_disconnected`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.odd_code_root_activity`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedRealization.odd_native_code_coloring`
- Dependency: [D5/S3/Combinatorics/Zigzag/DisconnectedMarking](DisconnectedMarking.md)
- Dependency: [D5/S3/Combinatorics/Zigzag/DisconnectedSupport](DisconnectedSupport.md)
