# Fixed-Charge Rigidity for the P48q Order-Three Lift

## Abstract

Surjectivity of the integral cyclic norm forces every mode-preserving cube-one lift of the Nebe order-three action to fix its fixed-charge ground states.

**Theorem 1.1 (The phase on a cyclic norm is trivial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeLiftRigidity.fixed_charge_phase_eq_one_of_cube_one_norm_image`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeLiftRigidity.fixed_charge_phase_eq_one_of_cube_one_norm_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be a cube-one isometry of an even integral lattice. Suppose every fixed charge is the sum of an orbit x, gx, g²x. Consider a complex-linear cube-one lift U that preserves the integer vertex modes and acts on each charged ground state by U(eₐ) = η(a)e₍gₐ₎.

Preserving the normalized ground product relates η(a+b) to η(a)η(b) by the ratio of the two cocycle signs. Apply this relation twice to the three orbit charges. Rotating the cocycle product past x introduces two equal skew signs, since the pairings of x with gx and g²x agree. The signs multiply to one. The cube identity makes η(x)η(gx)η(g²x) equal to one, which forces η(x+gx+g²x) to equal one.

**Theorem 1.2 (Every such P48q lift fixes the fixed-charge ground states).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeLiftRigidity.p48q_order_three_lift_standard`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeLiftRigidity.p48q_order_three_lift_standard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

Right multiplication by the concrete Nebe matrix is the order-three additive isometry of the catalogue lattice. The integral norm certificate supplies an orbit-sum preimage for every fixed row. Applying the general cyclic norm argument proves that the phase of every mode-preserving cube-one monomial lift equals one on all fixed charges.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeLiftRigidity.fixed_charge_phase_eq_one_of_cube_one_norm_image`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeLiftRigidity.p48q_order_three_lift_standard`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate](P48qFixedRankCertificate.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate](P48qGramCertificate.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNormImageCertificate](P48qNormImageCertificate.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorGround](../../Sectors/LatticeSectorGround.md)
