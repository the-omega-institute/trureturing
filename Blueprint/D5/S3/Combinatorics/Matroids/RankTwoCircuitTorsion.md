# Class potentials for rank-two matroids

## Abstract

Normalized parallel-class potentials for rank-two joint restriction.

**Theorem 1.1 (Recovering normalized class potentials).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion.exists_potentials_of_integral_readouts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion.exists_potentials_of_integral_readouts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bases are the pairs of vertices from distinct parallel classes. The residue of a rational edge coefficient is taken in the sign convention of the vertex boundary. Pair circuits identify the edge residues along each parallel class. Triangle circuits make the residues differences of class values. Fixing the value of one class to zero makes these values unique. Every class value is killed by the ground size, and the sum weighted by class sizes vanishes.

**Theorem 1.2 (Realizing normalized class potentials).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion.exists_integral_readouts_of_potentials`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion.exists_integral_readouts_of_potentials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose rational representatives of the class values and take their differences along the edges. The weighted equations make the resulting vertex boundaries integral. These boundaries sum to zero. Route the integral correction to one vertex along edges between classes, using a vertex in a second class when needed. Subtracting this correction gives a rational top cycle with the prescribed edge residues and integral readouts.

**Theorem 1.3 (Class potentials and the lifting quotient).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion.rank_two_lifting_obstruction_potentials`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion.rank_two_lifting_obstruction_potentials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient of the saturated joint image by the original image is isomorphic to the module of normalized class potentials. The residue has zero class potential exactly when the rational source has integral edge coefficients. Every class potential satisfying the boundary relations is realized by one source cycle.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion.exists_integral_readouts_of_potentials`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion.exists_potentials_of_integral_readouts`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion.rank_two_lifting_obstruction_potentials`
- Dependency: [D5/S3/Combinatorics/Matroids/RationalJointCircuitImage](RationalJointCircuitImage.md)
