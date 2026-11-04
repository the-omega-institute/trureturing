# Tribonacci Rauzy Fractal

## Abstract

The finite Tribonacci internal window has a compact Rauzy closure with the three admissible prefix contractions.

The construction starts from the existing bounded internal window at a non-Perron Tribonacci root. It proves nonemptiness, compactness, an explicit closed-ball bound, and invariance of the closure under the 0, 10, and 110 prefix maps. Exact attractor equality is left open for a later unit.

**Definition 1.1 (Rauzy closure).**

Lean statement: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal`

*Formalization.* `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closure of the finite Tribonacci internal window in the complex internal coordinate is the Rauzy fractal set.

**Definition 1.2 (Prefix contractions).**

Lean statement: `D5/S0/Tower/Tribonacci/RauzyFractal.zeroPrefixMap`

*Formalization.* `D5/S0/Tower/Tribonacci/RauzyFractal.zeroPrefixMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three maps are the complex affine maps induced by the admissible initial blocks 0, 10, and 110.

**Theorem 1.3 (Nonemptiness and compactness).**

Lean statement: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_isCompact`

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_isCompact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty name supplies the origin. The existing geometric-series bound makes the closure compact at every secondary root.

**Theorem 1.4 (Explicit window bound).**

Lean statement: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_subset_closedBall`

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_subset_closedBall` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closure lies in the closed ball centered at zero with radius (1 - ‖z‖)⁻¹.

**Theorem 1.5 (Prefix invariance).**

Lean statement: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_prefix_invariant`

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_prefix_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Admissibility transport is proved for each prefix, and continuity transports the inclusions through closure.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal`
- Truth anchor: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_isCompact`
- Truth anchor: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_prefix_invariant`
- Truth anchor: `D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_subset_closedBall`
- Truth anchor: `D5/S0/Tower/Tribonacci/RauzyFractal.zeroPrefixMap`
- Dependency: [D5/S0/Tower/Tribonacci/ModelSet](ModelSet.md)
- Dependency: [D5/S0/Tower/Tribonacci/Names](Names.md)
