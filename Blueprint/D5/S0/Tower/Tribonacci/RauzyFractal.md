# Tribonacci Rauzy Fractal

## Abstract

The finite Tribonacci internal window has a compact Rauzy closure with the three admissible prefix contractions.

The construction starts from the existing bounded internal window at a non-Perron Tribonacci root. It proves nonemptiness, compactness, an explicit closed-ball bound, and invariance of the closure under the `0`, `10`, and `110` prefix maps. Exact attractor equality is left open for a later unit.

**Definition 1.1 (Rauzy closure).**

Lean statement: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal`

*Formalization.* `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal` (`✓ std3`).

*Source.* Repository-derived.

**Definition 1.2 (Prefix contractions).**

Lean statements: `zeroPrefixMap`, `oneZeroPrefixMap`, and `oneOneZeroPrefixMap` in `D5/S0/Tower/Tribonacci/RauzyFractal`.

*Formalization.* The three maps are kernel-checked complex affine contractions induced by the admissible initial blocks `0`, `10`, and `110` (`✓ std3`).

*Source.* Repository-derived.

**Theorem 1.3 (Nonemptiness and compactness).**

Lean statements: `rauzyFractal_nonempty` and `rauzyFractal_isCompact`.

*Formalization.* The empty name supplies the origin. At every secondary root, the existing geometric-series bound makes the closure compact by Heine–Borel (`✓ std3`).

*Source.* Repository-derived.

**Theorem 1.4 (Explicit window bound).**

Lean statement: `rauzyFractal_subset_closedBall`.

*Formalization.* The closure lies in the closed ball centered at zero with radius `(1 - ‖z‖)⁻¹` (`✓ std3`).

*Source.* Repository-derived.

**Theorem 1.5 (Prefix invariance).**

Lean statements: `zeroPrefixMap_mapsTo_rauzyFractal`, `oneZeroPrefixMap_mapsTo_rauzyFractal`, `oneOneZeroPrefixMap_mapsTo_rauzyFractal`, and `rauzyFractal_prefix_invariant`.

*Formalization.* Finite admissibility transport is proved for each prefix, then continuity transports the inclusions through closure. The final theorem gives the three-map union inclusion into the Rauzy fractal (`✓ std3`).

*Source.* Repository-derived.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal`
- Truth anchor: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_isCompact`
- Truth anchor: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_prefix_invariant`
- Dependency: [D5/S0/Tower/Tribonacci/ModelSet](ModelSet.md)
- Dependency: [D5/S0/Tower/Tribonacci/Names](Names.md)
