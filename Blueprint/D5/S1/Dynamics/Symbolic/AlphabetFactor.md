# Continuous Alphabet Factors of Symbolic Systems

## Abstract

A continuous map between alphabets acts coordinatewise on full shifts.  This map is continuous, commutes with every translation shift, and sends a compact-alphabet closed subshift to a closed shift-invariant image subshift.

**Definition 1.1 (Coordinatewise alphabet map).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap`

*Formalization.* `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

`alphabetMap f x` applies `f` independently at each coordinate of the configuration `x`.

**Theorem 1.2 (Continuity of the coordinatewise map).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.continuous_alphabetMap`

*Formalization.* `D5/S1/Dynamics/Symbolic/AlphabetFactor.continuous_alphabetMap` (`✓ std3`).

*Source.* Repository-derived, using product-topology continuity.

*Commentary.*

Continuity of `f` lifts through the product projections to continuity of the full-shift map.

**Theorem 1.3 (Shift factor law).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap_shift`

*Formalization.* `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap_shift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Applying the alphabet map before or after a translation shift gives the same configuration.  The corresponding `alphabetMap_semiconj` packages this equality as a semiconjugacy.

**Theorem 1.4 (Closed image of a subshift).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.isClosed_image_subshift`

*Formalization.* `D5/S1/Dynamics/Symbolic/AlphabetFactor.isClosed_image_subshift` (`✓ std3`).

*Source.* Repository-derived, using compactness of the source product and Hausdorffness of the target product.

*Commentary.*

When the source alphabet is compact and the target alphabet is Hausdorff, the continuous image of the closed source subshift is compact and hence closed.

**Theorem 1.5 (Shift invariance of the image).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapsTo_image_subshift`

*Formalization.* `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapsTo_image_subshift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shift factor law transports the source subshift's invariance to its coordinatewise image.

**Definition 1.6 (Mapped subshift).**

Lean statement: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapSubshift`

*Formalization.* `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapSubshift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

`mapSubshift f hf X` bundles the closed, shift-invariant image into a `FullShift.Subshift` over the target alphabet.  Its carrier is exposed by `mapSubshift_carrier`.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.continuous_alphabetMap`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap_shift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.alphabetMap_semiconj`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.isClosed_image_subshift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapsTo_image_subshift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapSubshift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AlphabetFactor.mapSubshift_carrier`
