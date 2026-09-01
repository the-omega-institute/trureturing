# Weyl Displacement Words over a Finite Cyclic Window

## Abstract

Weyl displacement words compose with a phase fixed by the symplectic pairing.

**Definition 1.1 (The displacement word).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b: \operatorname{ZMod}(M),\ \operatorname{displacement}\left(M, a, b\right) = \operatorname{shiftMatrix}\left(M\right)^{\operatorname{val}\left(a\right)} \cdot \operatorname{clockMatrix}\left(M\right)^{\operatorname{val}\left(b\right)}.$$

*Formalization.* `D5/S3/Quantum/Algebra/WeylDisplacement.displacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displacement word at index (a, b) is the shift raised to the canonical natural representative of a, times the clock raised to the canonical natural representative of b. Both generators, their Weyl relation, their orders, and their unitarity are already frozen in the window register, which this module imports.

The finite Weyl-Heisenberg group these words generate is classical, so no novelty is claimed for them. Appleby (2005), Journal of Mathematical Physics 46, 052107, doi 10.1063/1.1896384, defines the extended Clifford group as the normalizer of that group. Only the bibliographic identity and the published abstract were checked; the full text was not read, so the article is cited as background and not as the source of the identities proved below.

**Theorem 1.2 (Composition law).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b, c, d: \operatorname{ZMod}(M),\ \operatorname{displacement}\left(M, a, b\right) \cdot \operatorname{displacement}\left(M, c, d\right) = \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(b \cdot c\right)} \cdot \operatorname{displacement}\left(M, {a + c}, {b + d}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two displacement words multiply to a third, scaled by a single window phase. The exponent of that phase is the clock index of the left factor times the shift index of the right factor, and nothing else. The proof moves a clock power across a shift power by iterating the frozen Weyl relation twice, once in each exponent.

Exponents are natural representatives of residues, so the identity needs the generators to see their exponents only modulo the window cardinality. That is supplied by the frozen order relations for the clock and the shift and by primitivity for the phase.

The pinned Mathlib source carries no Weyl-Heisenberg material: no file mentions the Weyl-Heisenberg group, the generalized Pauli group, or clock and shift matrices, and no file is named after Pauli or Heisenberg. The displacement words are nevertheless classical, so the cited article records that no novelty is claimed here.

**Theorem 1.3 (Squaring identity).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b: \operatorname{ZMod}(M),\ \operatorname{displacement}\left(M, a, b\right)^{2} = \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(a \cdot b\right)} \cdot \operatorname{displacement}\left(M, {a + a}, {b + b}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Setting the two indices equal in the composition law gives the square of a displacement word as the doubled word carrying the phase whose exponent is the product of the two indices.

**Theorem 1.4 (The composition phase is not vacuous).**

$$\operatorname{displacement}\left(2, 0, 1\right) \cdot \operatorname{displacement}\left(2, 1, 0\right) \neq \operatorname{displacement}\left(2, 1, 0\right) \cdot \operatorname{displacement}\left(2, 0, 1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_two_not_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The composition law would read the same way if every phase were one, so a witness is recorded that the phase does real work. On the two-address window the words at (0, 1) and (1, 0) do not commute. Assuming they did forces the window phase to be its own square, hence one, contradicting primitivity.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacement.displacement`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_mul`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_sq`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_two_not_commute`
- Dependency: [D5/S3/Observer/WindowRegister](../../Observer/WindowRegister.md)
