# Degrees over an abelian normal subgroup

## Abstract

Fixed-point-free conjugation on an abelian normal subgroup constrains simple complex degrees.

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

## References

- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree`
- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCharacterDegrees.degree_square_le_card`
- Dependency: [D5/S3/FiniteGroups/CharacterDegreeDivisibility](CharacterDegreeDivisibility.md)
- Dependency: [D5/S3/FiniteGroups/CliffordConstituents](CliffordConstituents.md)
- Dependency: [D5/S3/FiniteGroups/CliffordDecomposition](CliffordDecomposition.md)
- Dependency: [D5/S3/FiniteGroups/ComplexCharacterAbelianProducts](ComplexCharacterAbelianProducts.md)
- Dependency: [D5/S3/FiniteGroups/FiniteCharacterAlgebra](FiniteCharacterAlgebra.md)
- Dependency: [D5/S3/FiniteGroups/InducedCharacterFormula](InducedCharacterFormula.md)
