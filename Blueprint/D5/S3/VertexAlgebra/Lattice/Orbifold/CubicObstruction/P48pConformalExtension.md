# The P48p Extension Obstruction from the Conformal Action

## Abstract

The actual conformal action supplies the charge projection for the P48p extension obstruction.

**Theorem 1.1 (The conformal action forces weight-two dimension at least two).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pConformalExtension.p48p_associator_extension_obstruction_of_conformal_action`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pConformalExtension.p48p_associator_extension_obstruction_of_conformal_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be a positive-definite, rootless, even integral lattice of rank 48 with a specified complex left inverse of its Gram matrix. The finite group A acts faithfully by integral charge isometries and realizes every such isometry. A normal subgroup N has order dividing 2^4 * 3 * 11 * 23, index dividing 12, and an embedding into SL2(23). A subgroup L containing N acts irreducibly on the rational charge coordinates and agrees with A on integral charges. An involution in N mapping to negative identity is central in L, and L has a central element of order three outside N. The real Cartan fixed ranks at order three in L are zero or sixteen, at order eleven in N they are eight, and at order twenty-three in N they are four. The P48p group and rank inputs are carried over from the derived-action obstruction, which cites Nebe, arXiv:1212.0865, Theorem 3.6, proof (B), and Proposition 4.8.

A finite group G acts faithfully by complex linear equivalences. On its subgroup K the action preserves all integer modes of the actual lattice state field and fixes the inverse-Gram conformal vector. The conformal ground projection recovers a homomorphism from K to A and a complex unit phase for each element and charge. The action on a ground vector is multiplication by this phase on the ground vector at the projected charge. Restricting the codomain to the image gives the surjection required by the derived-action obstruction.

Assume the ambient associator on G restricts on K to the coboundary of a two-cochain. The type comparison is assumed for any element of K of ambient order three that obeys the monomial ground law for a charge isometry of order three and real Cartan fixed rank sixteen, with complex unit phase one on every fixed charge. Its cyclic pullback of the ambient associator equals the type-one carry representative times an explicit two-coboundary, using a complex unit of exact order three in the convention of Evans and Gannon, arXiv:1804.11145, equations (2.13) and (2.14). The recovered projection and phase supply the monomial law for this comparison.

An injective linear inclusion of the K-invariant lattice states sends grade two into the finite-dimensional eigenvalue-two eigenspace of the target weight operator. The derived-action obstruction then gives dimension at least two for that eigenspace.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pConformalExtension.p48p_associator_extension_obstruction_of_conformal_action`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport](../../Automorphisms/ConformalGroundTransport.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pDerivedExtension](P48pDerivedExtension.md)
