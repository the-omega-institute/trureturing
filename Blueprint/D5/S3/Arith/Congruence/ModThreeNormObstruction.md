# The Mod-Three Quadratic Norm Obstruction

## Abstract

An integer congruent to two modulo three is not a norm of the form x^2 + 3y^2.

**Theorem 1.1 (No number 3m - 1 is an x^2 + 3y^2 norm).**

$$\forall m, x, y \in \mathbb{Z},\ x^{2}+3y^{2} \neq 3m-1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ModThreeNormObstruction.three_mul_sub_one_not_quadratic_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers m, x, and y, the equality x^2 + 3y^2 = 3m - 1 is impossible. Reduction modulo three kills both terms carrying a factor three, leaving x^2 = 2 in ZMod 3, while a square modulo three is only zero or one.

The repository was searched before construction. The lower-layer theorem ZeroOrbitCongruence.eisenstein_norm_mod_three supplies the square-residue dichotomy by specialization at its second variable zero, and is applied directly. Pinned Mathlib text search found only packaged modulo-four square obstructions, and the exact Loogle query for a square in ZMod 3 unequal to two returned no declaration.

This node closes only the explicit claim in appendix E.52 that an integer in the residue class two modulo three cannot be such a quadratic norm. It does not formalize the full Markov-geodesic avoidance theorem, the trace reduction, the crossing-spectrum lower bound, or the numerical certificate.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ModThreeNormObstruction.three_mul_sub_one_not_quadratic_norm`
- Dependency: [D5/S1/Phase/ZeroOrbitCongruence](../../../S1/Phase/ZeroOrbitCongruence.md)
