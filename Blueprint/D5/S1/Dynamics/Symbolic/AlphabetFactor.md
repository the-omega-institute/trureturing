# Continuous Alphabet Factors of Symbolic Systems

## Abstract

Continuous alphabet maps induce compact shift-equivariant factor subshifts.

A continuous map between alphabets acts coordinatewise on full shifts. This map is continuous, commutes with every translation shift, and sends a compact-alphabet closed subshift to a closed shift-invariant image subshift.

**Definition 1.1 (Coordinatewise alphabet map).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap`

*Formalization.* `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

alphabetMap f x applies f independently at each coordinate of the configuration x.

**Theorem 1.2 (Continuity of the coordinatewise map).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.continuous_alphabetMap`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/AlphabetFactor.continuous_alphabetMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity of f lifts through product projections to continuity of the full-shift map.

**Theorem 1.3 (Shift factor law).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the alphabet map before or after a translation shift gives the same configuration; alphabetMap_semiconj packages this equality as a semiconjugacy.

**Theorem 1.4 (Coordinatewise semiconjugacy).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap_semiconj`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap_semiconj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each translation parameter, the coordinatewise alphabet map is a semiconjugacy between the source and target full-shift actions.

**Theorem 1.5 (Closed image of a subshift).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.isClosed_image_subshift`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/AlphabetFactor.isClosed_image_subshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A compact source alphabet and Hausdorff target alphabet make the continuous image of a closed subshift compact and therefore closed.

**Theorem 1.6 (Shift invariance of the image).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapsTo_image_subshift`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapsTo_image_subshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shift factor law transports source subshift invariance to the coordinatewise image.

**Definition 1.7 (Mapped subshift).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapSubshift`

*Formalization.* `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapSubshift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

mapSubshift f hf X bundles the closed, shift-invariant image into a FullShift.Subshift over the target alphabet.

**Theorem 1.8 (Carrier of the mapped subshift).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapSubshift_carrier`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapSubshift_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier of mapSubshift is definitionally the coordinatewise image.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap_semiconj`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap_shift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.continuous_alphabetMap`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.isClosed_image_subshift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapSubshift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapSubshift_carrier`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapsTo_image_subshift`
