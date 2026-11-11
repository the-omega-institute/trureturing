# The three-point Fourier root obstruction

## Abstract

Unit-circle rigidity for a three-term Fourier mask.

This is the algebraic bottleneck in the one-dimensional three-point tiling route toward the six-cell Nivat boundary. Two unit-modulus phases whose sum with one is zero must be cubic roots of unity; the result is conditional input for the later Fourier/Newman rigidity argument.

**Theorem 1.1 (Unit-circle root rigidity).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanThreePointRoot.unit_circle_three_term_root`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanThreePointRoot.unit_circle_three_term_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex u and v of norm one, if 1 + u + v = 0 then both satisfy z^2 + z + 1 = 0.

**Theorem 1.2 (Cubic phase consequence).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanThreePointRoot.unit_circle_three_term_root_cubed`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanThreePointRoot.unit_circle_three_term_root_cubed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same hypotheses imply u^3 = v^3 = 1, isolating the cubic character constraint used by the six-cell section argument.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanThreePointRoot.unit_circle_three_term_root`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanThreePointRoot.unit_circle_three_term_root_cubed`
