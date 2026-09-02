# Conjugation of Weyl Displacement Words

## Abstract

Conjugating a displacement word by another rescales it by the symplectic phase.

**Theorem 1.1 (Conjugation law).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b, c, d: \operatorname{ZMod}(M),\ \operatorname{displacement}\left(M, a, b\right) \cdot \operatorname{displacement}\left(M, c, d\right) \cdot \operatorname{star}\left(\operatorname{displacement}\left(M, a, b\right)\right) = \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(b \cdot c - a \cdot d\right)} \cdot \operatorname{displacement}\left(M, c, d\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementConjugation.displacement_conjugation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating the displacement word D (c, d) by D (a, b) gives back D (c, d), scaled by a single root of unity whose exponent is the symplectic pairing b * c - a * d of the two index pairs.

The proof composes two already-frozen laws of this family, the composition law and the adjoint law. The phase bookkeeping is redone locally because the corresponding helper in the frozen module is private and frozen modules are not amended.

The exponent is antisymmetric under swapping the two index pairs, which can be read off the displayed statement. Nothing beyond that is claimed: this node asserts no criterion for when two words commute, and nothing about commutation subgroups, Clifford groups, or representation theory.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementConjugation.displacement_conjugation`
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementAdjoint](WeylDisplacementAdjoint.md)
