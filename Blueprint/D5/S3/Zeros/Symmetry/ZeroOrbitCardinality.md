# Zero Orbit Cardinality

## Abstract

Off the critical line, a supplied nonreal zero index has a four-point symmetry orbit.

**Theorem 1.1 (An off-line zero index has a four-point orbit).**

$$\forall Z: \operatorname{ZeroData},\ \forall n\in \mathbb{N},\ Z.conjugation(n) \neq n \land \Re(Z.zero(n)) \neq \operatorname{criticalAbscissa} \Rightarrow \operatorname{card}\{n, Z.reflection(n), Z.conjugation(n), Z.conjugation(Z.reflection(n))\} = 4.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ZeroOrbitCardinality.zero_orbit_card_four_of_off_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditional on a supplied duplicate-free exhaustive ZeroData enumeration, an index with a distinct conjugation partner and an off-critical-line zero has exactly four indices in its reflection-conjugation orbit. The proof uses the public commutation, mirror fixed-point, and involution theorems to establish pairwise distinctness. It constructs no ZeroData inhabitant, asserts no off-line zero exists, and makes no Riemann hypothesis claim.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/ZeroOrbitCardinality.zero_orbit_card_four_of_off_line`
- Dependency: [D5/S3/Zeros/Symmetry/ZeroSymmetryAction](ZeroSymmetryAction.md)
