# Icosahedral Exterior-Square Decomposition

## Abstract

The real A5 exterior square splits into its two Galois-conjugate icosahedral summands.

**Theorem 1.1 (The second exterior power is the complete icosahedral pair).**

$$\forall rho3 \in \operatorname{Representation}\left(Real, A5, \operatorname{Pi}\left(Fin3, Real\right)\right), rho3Prime \in \operatorname{Representation}\left(Real, A5, \operatorname{Pi}\left(Fin3, Real\right)\right),\; \left(\operatorname{IsIrreducible}\left(rho3\right) \land \left(\operatorname{IsIrreducible}\left(rho3Prime\right) \land \left(\operatorname{GoldenGaloisCharacterPair}\left(rho3, rho3Prime\right) \land \operatorname{character}\left(secondOrderRepresentation\right) = \operatorname{character}\left(rho3\right) + \operatorname{character}\left(rho3Prime\right)\right)\right)\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{RepresentationEquiv}\left(secondOrderRepresentation, \operatorname{prod}\left(rho3, rho3Prime\right)\right)\right) \land \operatorname{Nonempty}\left(\operatorname{RealLinearEquiv}\left(IcosahedralCompletionSpace, SecondOrderObservationSpace\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Representation/IcosahedralExteriorSquareDecomposition.exterior_square_decomposes_into_icosahedral_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here A5 is the concrete alternatingGroup on Fin 5. The standard state V4 is the real subspace of five coordinates with zero sum, acted on by even coordinate permutations, and the second-order representation is the induced action on the genuine exterior power Lambda^2 V4.

The parameters rho3 and rho3Prime are representations on two real three-dimensional carriers. Their two irreducibility premises and the GoldenGaloisCharacterPair premise carry exactly the source identification of V3 and V3Prime as distinct golden Galois-conjugate icosahedral irreducibles. The final premise is the character-sum equality calculated in the source proof.

The first conclusion is a genuine A5-equivariant linear equivalence from Lambda^2 V4 to the product representation rho3.prod rho3Prime. The second conclusion separately records the induced real linear equivalence from the six-dimensional product carrier to the complete second-order observation space; neither leaf is merely a character or dimension equality.

Pinned Mathlib supplies the character inner-product formula, Schur injectivity, and Maschke splitting. Distinctness kills both cross intertwiner spaces; nonzero embeddings of the two irreducibles then have disjoint images, and character equality at the identity shows that their copairing exhausts the exterior square.

## References

- Truth anchor: `D5/S3/Arith/Representation/IcosahedralExteriorSquareDecomposition.exterior_square_decomposes_into_icosahedral_pair`
- Dependency: [D5/S0/Carrier/Conj](../../../S0/Carrier/Conj.md)
- Dependency: [D5/S1/Scale/Embedding](../../../S1/Scale/Embedding.md)
