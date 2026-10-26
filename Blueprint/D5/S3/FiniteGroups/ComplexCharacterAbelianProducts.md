# Irreducible representations of products with abelian groups

## Abstract

Restriction past an abelian direct factor preserves irreducibility over an algebraically closed field.

**Theorem 1.1 (Central elements act by scalars).**

$$\forall k \in Type*,\; [Field\left(k\right)], [IsAlgClosed\left(k\right)], \forall V \in Type*,\; [AddCommGroup\left(V\right)], [Module\left(k\right)\left(V\right)], [FiniteDimensional\left(k\right)\left(V\right)], \forall G \in Type*,\; [Monoid\left(G\right)], \forall rho \in Representation\left(k, G, V\right),\; [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], \forall z \in G,\; (\forall g \in G,\; z \cdot g = g \cdot z) \Rightarrow (\exists c \in k,\; rho\left(z\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(c, (\operatorname{LinearMap}.\operatorname{id}: LinearMap\left(k, V, V\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/ComplexCharacterAbelianProducts.central_action_scalar` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

Schur's lemma identifies an intertwining endomorphism with scalar multiplication. A central group element gives such an endomorphism.

**Theorem 1.2 (The same simple degrees).**

$$\forall B \in Type,\; [Group\left(B\right)], \forall A \in Type,\; [CommGroup\left(A\right)], \{d: \mathbb{N} | \exists X \in FDRep\left(\mathbb{C}, (B \times A)\right),\; \operatorname{CategoryTheory}.\operatorname{Simple}\left(X\right) \land \operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, X\right) = d\} = \{d: \mathbb{N} | \exists X \in FDRep\left(\mathbb{C}, B\right),\; \operatorname{CategoryTheory}.\operatorname{Simple}\left(X\right) \land \operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, X\right) = d\}$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/ComplexCharacterAbelianProducts.degreesProdAbelian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The abelian second factor acts by scalars. Every subspace invariant under the first factor is therefore invariant under the whole product.

## References

- Truth anchor: `D5/S3/FiniteGroups/ComplexCharacterAbelianProducts.central_action_scalar`
- Truth anchor: `D5/S3/FiniteGroups/ComplexCharacterAbelianProducts.degreesProdAbelian`
- Dependency: [D5/S3/FiniteGroups/FiniteCharacterAlgebra](FiniteCharacterAlgebra.md)
