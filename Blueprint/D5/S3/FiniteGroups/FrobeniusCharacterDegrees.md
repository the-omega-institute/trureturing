# Degrees over normal subgroups

## Abstract

Fixed-point-free conjugation gives a structural alternative for simple representations in every characteristic and integer degree dichotomies over the complex numbers.

**Theorem 1.1 (The degree-square bound).**

$$\forall G \in Type,\; [Group\left(G\right)], [Finite\left(G\right)], \forall X \in FDRep\left(\mathbb{C}, G\right),\; [\operatorname{CategoryTheory}.\operatorname{Simple}\left(X\right)], \operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, X\right)^{2} \le \operatorname{Nat}.\operatorname{card}\left(G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.degree_square_le_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The group algebra maps onto the endomorphism algebra of a simple representation. Comparing dimensions bounds the square of its degree by the group order.

**Theorem 1.2 (The divisibility dichotomy).**

$$\forall K \in Type,\; [Group\left(K\right)], [Finite\left(K\right)], \forall N \in Subgroup\left(K\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [IsMulCommutative\left(N\right)], (\forall g \in K,\; (\neg g \in N) \Rightarrow (\forall n \in N,\; (\operatorname{MulAut}.\operatorname{conjNormal}\left(g, n\right) = n) \Rightarrow (n = 1))) \Rightarrow (\forall W \in FDRep\left(\mathbb{C}, K\right),\; [\operatorname{CategoryTheory}.\operatorname{Simple}\left(W\right)], (\operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, W\right) \mid \operatorname{Subgroup}.\operatorname{index}\left(N\right)) \lor (\operatorname{Subgroup}.\operatorname{index}\left(N\right) \mid \operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, W\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

A nontrivial simple constituent of the restriction has inertia subgroup equal to the normal subgroup. Clifford decomposition then makes the subgroup index divide the degree. A trivial constituent makes the representation descend to the quotient, where its degree divides the quotient order.

**Theorem 1.3 (Character invariance forces triviality).**

$$\forall A \in Type,\; [Group\left(A\right)], [Finite\left(A\right)], \forall alpha \in MulAut\left(A\right),\; (\forall a \in A,\; (alpha\left(a\right) = a) \Rightarrow (a = 1)) \Rightarrow (\forall V \in FDRep\left(\mathbb{C}, A\right),\; [\operatorname{CategoryTheory}.\operatorname{Simple}\left(V\right)], (\forall a \in A,\; \operatorname{FDRep}.\operatorname{character}\left(V, alpha\left(a\right)\right) = \operatorname{FDRep}.\operatorname{character}\left(V, a\right)) \Rightarrow (\operatorname{Representation}.\operatorname{IsTrivial}\left(\operatorname{FDRep}.\rho\left(V\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.trivial_of_character_invariant_fixedPointFree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

Assume a simple representation has character invariant under a fixed-point-free automorphism. Character orthogonality supplies an isomorphism with the twisted representation, hence an invertible intertwiner. Surjectivity of the Lang map makes its twisted traces constant. Density extends the resulting trace identities to every endomorphism, and rank-one trace pairings force the representation to be trivial.

**Theorem 1.4 (The nonabelian divisibility dichotomy).**

$$\forall K \in Type,\; [Group\left(K\right)], [Finite\left(K\right)], \forall N \in Subgroup\left(K\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], (\forall g \in K,\; (\neg g \in N) \Rightarrow (\forall n \in N,\; (\operatorname{MulAut}.\operatorname{conjNormal}\left(g, n\right) = n) \Rightarrow (n = 1))) \Rightarrow (\forall W \in FDRep\left(\mathbb{C}, K\right),\; [\operatorname{CategoryTheory}.\operatorname{Simple}\left(W\right)], (\operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, W\right) \mid \operatorname{Subgroup}.\operatorname{index}\left(N\right)) \lor (\operatorname{Subgroup}.\operatorname{index}\left(N\right) \mid \operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, W\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree_nonabelian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The same Clifford argument works for an arbitrary finite normal subgroup. Character invariance under an inertia conjugation is first converted to triviality by the trace-rigidity theorem, so a nontrivial constituent has inertia exactly the kernel; the two Clifford branches give the stated divisibility alternatives.

**Theorem 1.5 (Twist equivalence forces trivial action in every characteristic).**

$$\forall k \in Type*,\; [Field\left(k\right)], [IsAlgClosed\left(k\right)], \forall A \in Type*,\; [Group\left(A\right)], [Finite\left(A\right)], \forall alpha \in MulAut\left(A\right),\; \forall hAlpha \in \left(\forall a \in A,\; (alpha\left(a\right) = a) \Rightarrow (a = 1)\right),\; \forall V \in FDRep\left(k, A\right),\; [\operatorname{CategoryTheory}.\operatorname{Simple}\left(V\right)], \forall e \in \operatorname{Representation}.\operatorname{Equiv}\left(\operatorname{FDRep}.\rho\left(V\right), \operatorname{FDRep}.\rho\left(V\right).\operatorname{comp}\left(\operatorname{MulAut}.\operatorname{toMonoidHom}\left(alpha\right)\right)\right),\; \operatorname{Representation}.\operatorname{IsTrivial}\left(\operatorname{FDRep}.\rho\left(V\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.trivial_of_equiv_fixedPointFree_of_isAlgClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

Let k be algebraically closed and A finite. The displayed e is an actual equivalence between the simple finite-dimensional representation and its twist; equality of traces is not substituted for this hypothesis. Its invertible intertwiner T satisfies T rho(a) = rho(alpha(a)) T. The fixed-point-free commutator map is surjective, so cyclic invariance of trace makes tr(T rho(a)) constant. Applying this also to products, and extending linearly through k[A], gives tr(U (T rho(a) - T)) = 0 for every endomorphism U, by density. Rank-one endomorphisms detect every vector under the trace pairing in every characteristic. Thus T rho(a) = T, and injectivity of T proves trivial action. This is the repository's derivation from classical density and the fixed-point-free commutator lemma; no novelty or characteristic-zero argument is claimed.

**Theorem 1.6 (Invariant simple characters give trivial action in every characteristic).**

$$\forall k \in Type*,\; [Field\left(k\right)], [IsAlgClosed\left(k\right)], \forall A \in Type*,\; [Group\left(A\right)], [Finite\left(A\right)], \forall alpha \in MulAut\left(A\right),\; \forall hAlpha \in \left(\forall a \in A,\; (alpha\left(a\right) = a) \Rightarrow (a = 1)\right),\; \forall V \in FDRep\left(k, A\right),\; [\operatorname{CategoryTheory}.\operatorname{Simple}\left(V\right)], \forall hChi \in \left(\forall a \in A,\; \operatorname{FDRep}.\operatorname{character}\left(V, alpha\left(a\right)\right) = \operatorname{FDRep}.\operatorname{character}\left(V, a\right)\right),\; \operatorname{Representation}.\operatorname{IsTrivial}\left(\operatorname{FDRep}.\rho\left(V\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.trivial_of_character_invariant_fixedPointFree_of_isAlgClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

Here FDRep packages finite dimensionality and Simple V supplies irreducibility. The character hypothesis is pointwise on every a in A. Twisting by the automorphism preserves irreducibility, and simple-character separation over the algebraically closed field turns this hypothesis into a genuine equivalence with the twist. The preceding intertwiner and density argument then proves triviality. This repository derivation uses ordinary k-valued characters of simple modules; it uses neither division by the group order nor characteristic-zero orthogonality. The earlier complex theorem and its complex divisibility consequences retain their stated scopes.

**Theorem 1.7 (A structural Frobenius alternative over an algebraically closed field).**

$$\forall k \in Type*,\; [Field\left(k\right)], [IsAlgClosed\left(k\right)], \forall K \in Type,\; [Group\left(K\right)], [Finite\left(K\right)], \forall N \in Subgroup\left(K\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall hfix \in \left(\forall g \in K,\; (\neg g \in N) \Rightarrow (\forall n \in N,\; (\operatorname{MulAut}.\operatorname{conjNormal}\left(g, n\right) = n) \Rightarrow (n = 1))\right),\; \forall W \in FDRep\left(k, K\right),\; [\operatorname{CategoryTheory}.\operatorname{Simple}\left(W\right)], (\operatorname{Representation}.\operatorname{IsTrivial}\left(\operatorname{FDRep}.\rho\left(W\right).\operatorname{comp}\left(\operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)) \lor (\operatorname{Subgroup}.\operatorname{index}\left(N\right) \mid \operatorname{Module}.\operatorname{finrank}\left(k, W\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.trivial_restriction_or_index_dvd_of_fixedPointFree_of_isAlgClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

Let K be a finite group and N a normal subgroup, with every conjugation by an element outside N fixing only the identity of N. Clifford restriction chooses a simple N-constituent V and a multiplicity e. For a nontrivial V, membership in its inertia subgroup is equivalent to an isomorphism with the conjugate constituent. The existing FDRep-isomorphism/representation-equivalence bridge gives the twist equivalence, so fixed-point-free rigidity excludes every inertia element outside N. Since N lies in the inertia group, inertia equals N and the orbit has N.index elements. The generic Clifford formula is an equality of natural numbers: finrank_k W = e * inertia.index * finrank_k V. It therefore gives N.index dividing finrank_k W, with witness e * finrank_k V. In the trivial-constituent branch, every conjugate constituent has trivial action, hence so does the product module defining the Clifford sum. The actual Clifford isomorphism, the shrink equivalence and injectivity transport trivial action back to the restriction of W. This branch uses no character-equals-dimension test. In characteristic p the trace of the identity is only the image of the natural-number dimension in k: p and zero have the same image. Such field-valued equalities cannot certify natural-number divisibility or the converse implication from constant character to triviality for arbitrary modules (p copies of a module already have zero character). The surviving arithmetic statement comes from the natural-number Clifford formula. This result does not replace trivial restriction by the assertion that finrank_k W divides N.index in positive characteristic. The four earlier complex results, including their full integer degree dichotomies, remain separate. Density, Clifford theory and this synthesis are classical mathematics, not a claim of literature novelty.

## References

- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree`
- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree_nonabelian`
- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.degree_square_le_card`
- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.trivial_of_character_invariant_fixedPointFree`
- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.trivial_of_character_invariant_fixedPointFree_of_isAlgClosed`
- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.trivial_of_equiv_fixedPointFree_of_isAlgClosed`
- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.trivial_restriction_or_index_dvd_of_fixedPointFree_of_isAlgClosed`
- Dependency: [D5/S3/FiniteGroups/CharacterDegreeDivisibility](CharacterDegreeDivisibility.md)
- Dependency: [D5/S3/FiniteGroups/CliffordConstituents](CliffordConstituents.md)
- Dependency: [D5/S3/FiniteGroups/CliffordDecomposition](CliffordDecomposition.md)
- Dependency: [D5/S3/FiniteGroups/ComplexCharacterAbelianProducts](ComplexCharacterAbelianProducts.md)
- Dependency: [D5/S3/FiniteGroups/FiniteCharacterAlgebra](FiniteCharacterAlgebra.md)
- Dependency: [D5/S3/FiniteGroups/InducedCharacterFormula](InducedCharacterFormula.md)
