# Two-Torsion Weyl Displacement Identities

## Abstract

At a two-torsion index, a displacement word and its overlap with a self-adjoint matrix obey phase-weighted conjugation identities.

**Lemma 1.1 (Adjoint at a two-torsion index).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b: \operatorname{ZMod}(M),\ {a + a = 0} \implies {b + b = 0} \implies \operatorname{star}\left(\operatorname{displacement}\left(M, a, b\right)\right) = \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(a \cdot b\right)} \cdot \operatorname{displacement}\left(M, a, b\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementTwoTorsion.star_displacement_of_two_torsion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both residue indices are two-torsion, each is equal to its own negative. Substituting these equalities into the displacement adjoint law leaves the original displacement word multiplied by the stated window phase.

**Theorem 1.2 (Conjugation of a two-torsion overlap).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b: \operatorname{ZMod}(M),\ {a + a = 0} \implies {b + b = 0} \implies \forall rho: \operatorname{Matrix}\left(\operatorname{ZMod}\left(M\right), \operatorname{ZMod}\left(M\right), \mathbb{C}\right),\ {\operatorname{star}\left(rho\right) = rho} \implies \operatorname{star}\left(\operatorname{trace}\left(rho \cdot \operatorname{displacement}\left(M, a, b\right)\right)\right) = \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(a \cdot b\right)} \cdot \operatorname{trace}\left(rho \cdot \operatorname{displacement}\left(M, a, b\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementTwoTorsion.two_torsion_overlap_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a self-adjoint matrix, conjugating the trace pairing reverses the product under the adjoint. The two-torsion adjoint identity and cyclicity of the trace then give the displayed phase times the original pairing.

The result is only this conjugation identity. It makes no claim about density matrices, spectra, or geometric location.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementTwoTorsion.star_displacement_of_two_torsion`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementTwoTorsion.two_torsion_overlap_conj`
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementAdjoint](WeylDisplacementAdjoint.md)
