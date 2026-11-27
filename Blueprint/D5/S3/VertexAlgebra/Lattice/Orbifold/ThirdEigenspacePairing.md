# Complementary Cubic Eigenspaces of P48q

## Abstract

The complex P48q Gram form pairs the two primitive cubic eigenspaces perfectly and gives dual current bases indexed by Fin 16.

**Theorem 1.1 (Orthogonality for eigenvalues whose product differs from one).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.eigenspace_pairing_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.eigenspace_pairing_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a complex-linear endomorphism preserving a complex bilinear form B. If x and y are in the eigenspaces for α and μ and αμ differs from one, then B(x,y) = 0. Invariance gives B(x,y) = αμ B(x,y), and the difference of the two scalar factors is invertible.

**Definition 1.2 (The restricted pairing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.movingPairing`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.movingPairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an endomorphism A, a bilinear form B and a complex scalar ζ, restrict the first argument of B to the ζ eigenspace and the second to the ζ² eigenspace.

**Theorem 1.3 (The primitive cubic eigenspaces pair perfectly).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.movingPairing_isPerfPair`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.movingPairing_isPerfPair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the complex vector space is finite-dimensional, A³ is the identity, ζ is a primitive cube root, and B is nondegenerate and preserved by A. The restriction of B to the ζ and ζ² eigenspaces is perfect.

The cyclic averages (x + α²Ax + αA²x)/3 for α equal to 1, ζ and ζ² lie in the corresponding eigenspaces and sum to x. A vector in either moving eigenspace that pairs to zero with the opposite space also pairs to zero with the fixed space and its own eigenspace by orthogonality. The decomposition then puts it in a radical of B, where it vanishes. Both restricted radicals therefore vanish, giving the dual equivalences in finite dimension.

**Definition 1.4 (The complex row action).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qAction`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

The P48q endomorphism on complex functions on Fin 48 is the scalar extension of the catalogue row action x ↦ xM.

**Definition 1.5 (The complex Gram form).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qForm`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qForm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

The P48q bilinear form on complex functions on Fin 48 is the form with matrix G, the catalogue integer Gram matrix cast to the complex numbers.

**Theorem 1.6 (The row action preserves the complex Gram form).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qForm_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qForm_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

For any two complex rows x and y, the pairing of xM with yM equals the pairing of x with y. This follows by casting the integral identity MGMᵀ = G and evaluating the resulting bilinear forms.

**Theorem 1.7 (The complex Gram form has zero radicals).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qForm_nondegenerate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qForm_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

The integral left inverse remains a left inverse over the complex numbers. Taking determinants gives a product equal to one, so the complex Gram matrix is nonsingular and the bilinear form is nondegenerate.

**Theorem 1.8 (The cyclic average is fixed).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qAverage_mem_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qAverage_mem_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

For every complex row x and the P48q action A, the vector (x + Ax + A²x)/3 belongs to the kernel of A − 1. Applying A cycles the three summands because A³ is the identity.

**Theorem 1.9 (The P48q moving pairing is perfect).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_movingPairing_isPerfPair`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_movingPairing_isPerfPair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

For every primitive complex cube root ζ, the P48q Gram form restricts to a perfect pairing of the ζ eigenspace with the ζ² eigenspace. The cube, isometry and inverse identities supply the hypotheses of the general pairing theorem.

**Theorem 1.10 (Each P48q moving eigenspace is totally isotropic).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_moving_isotropic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_moving_isotropic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

For every primitive complex cube root ζ, the Gram pairing of any two vectors from the ζ eigenspace is zero, and the same holds for two vectors from the ζ² eigenspace. The squared eigenvalues are respectively ζ² and ζ, both different from one.

**Theorem 1.11 (Both moving eigenspaces have dimension sixteen).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_moving_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_moving_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

For every primitive complex cube root ζ, the ζ and ζ² eigenspaces each have complex dimension sixteen. The three distinct eigenspaces form a direct sum of total dimension forty-eight. The fixed-rank certificate gives sixteen fixed dimensions, and perfectness makes the two remaining dimensions equal.

**Definition 1.12 (Basis for the residue-one currents).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qBasis`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each primitive complex cube root ζ, choose a basis indexed by Fin 16 of the ζ eigenspace, using its dimension.

**Definition 1.13 (Dual basis for the residue-two currents).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qOppositeBasis`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qOppositeBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each primitive complex cube root ζ, transport the coordinate dual of the chosen ζ basis to the ζ² eigenspace through the inverse of the linear equivalence induced by the flipped perfect pairing. The resulting basis uses the same Fin 16 indices.

**Theorem 1.14 (The Gram matrix between the moving bases is the identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_pair_bases`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_pair_bases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every primitive complex cube root ζ and indices i,j in Fin 16, pairing the ith residue-one vector with the jth residue-two vector gives one when i = j and zero otherwise. These entries give the matching coefficients for creation and annihilation on the two fractional current grids.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.eigenspace_pairing_eq_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.movingPairing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.movingPairing_isPerfPair`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qAction`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qAverage_mem_fixed`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qForm`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qForm_invariant`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qForm_nondegenerate`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48qOppositeBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_movingPairing_isPerfPair`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_moving_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_moving_isotropic`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.p48q_pair_bases`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate](P48qFixedRankCertificate.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate](P48qGramCertificate.md)
