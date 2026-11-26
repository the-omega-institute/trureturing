# The Complementary Grids of the Third Cover

## Abstract

The full third-cover Virasoro representation splits into the ordinary central-charge-one action and a concrete complementary central-charge-two action.

Retain the two native residue grids with indices indivisible by three. The full rank-one covering action is ThirdCoverVirasoro.coverMode, of central charge three, and its scalar shift at zero is 1/9. ThirdCoverIntegerFactor identifies the divisible-by-three summands with the ordinary charge-one action. The remaining polynomial factor is constructed explicitly below by pointwise finite normal ordering.

**Definition 1.1 (Native complementary oscillator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.complementMode`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.complementMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive native index k+1 not divisible by three acts as (k+1) times partial differentiation in its complementary variable. The negative mode -(k+1) acts by multiplication by that variable. Divisible indices and zero act by zero.

**Theorem 1.2 (A complementary native mode acts on the second factor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.mode_join_complement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.mode_join_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonzero scaling of the ordinary variables, a native mode with index indivisible by three acts on join(P tensor Q) as join(P tensor complementMode(r)(Q)). The derivative of the ordinary renamed polynomial in that variable vanishes, and the creation case uses the complementary generator formula.

**Theorem 1.3 (Complementary modes on all split states).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.split_complementMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.split_complementMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

By tensor extensionality, conjugating an indivisible native mode by split gives the identity tensor complementMode(r).

**Definition 1.4 (Normal order on the complementary factor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.complementPair`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.complementPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the two complementary native modes with the smaller index on the left. The larger index acts first, as in the native normalPair definition.

**Definition 1.5 (Fractional Virasoro operators).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalVirasoro`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalVirasoro` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each integer m, use one third of one half of the normal-ordered sum with pairs (3m-k,k) over k indivisible by three, and add 1/9 times the identity at m=0. The support bound is transported from the full native action through the ordinary vacuum slice. Additivity and complex linearity follow from pointwise finite support.

**Theorem 1.6 (Complement of the integral Sugawara sum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.cover_sub_integer_join_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.cover_sub_integer_join_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero s, subtract integerSugawara(m) from the merged coverMode(m) acting on join(P tensor Q). The finite sum separates into the complementary and integral index sets, and both indices 3m-k and k are complementary together. Transport the remaining pairs through join to obtain join(P tensor fractionalVirasoro(m)(Q)).

**Theorem 1.7 (Complement operator on all split states).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.split_cover_sub_integer`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.split_cover_sub_integer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pure-tensor subtraction implies that conjugation sends the cover minus its integral summand to identity tensor fractionalVirasoro(m).

**Theorem 1.8 (Factorization of the full cover).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.split_coverMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.split_coverMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex s with s squared equal to three, conjugation by split sends coverMode(m) to L(m) tensor identity plus identity tensor fractionalVirasoro(m). This follows by adding the ordinary Sugawara intertwiner to the complementary subtraction.

**Theorem 1.9 (Virasoro law at central charge two).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalVirasoro_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalVirasoro_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers n and m, the commutator equals (n-m) fractionalVirasoro(n+m) plus 2(n^3-n)/12 times the identity when n+m=0. Under split the two factor actions commute. Conjugate the merged cover commutator at charge three, subtract the native L commutator at charge one, and cancel the injective tensor extension. Injectivity follows by evaluating on 1 tensor Q and applying join.

**Theorem 1.10 (Highest-weight vacuum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalVirasoro_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalVirasoro_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative integer m, fractionalVirasoro(m)(1) is 1/9 times 1 if m=0 and zero otherwise. In each pair with sum 3m, the larger index is nonnegative and therefore annihilates the constant polynomial before the other mode acts.

**Definition 1.11 (Normalized complementary current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalCurrent`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply complementMode(r) by the inverse of the chosen square root of three. The frequency r/3 lies in the complementary grids when r is indivisible by three.

**Theorem 1.12 (Heisenberg bracket on the complementary factor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalCurrent_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalCurrent_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

When r and t are indivisible by three, the commutator equals r/3 times the identity if r+t=0 and zero otherwise. Conjugate the first component of ThirdCoverVirasoro.current_commutator and use the second-factor current intertwiner and tensor injectivity. Bakalov and Kac, arXiv:math/0402315v1, equation (4.23), gives the fractional Heisenberg bracket convention. The concrete factor proof here is a repository derivation.

This establishes a concrete polynomial oscillator factor and its operator relations. The identification with a full lattice twisted-module state-field action and the sixteen-pair assembly require additional constructions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.complementMode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.complementPair`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.cover_sub_integer_join_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalCurrent_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalVirasoro`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalVirasoro_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.fractionalVirasoro_vacuum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.mode_join_complement`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.split_complementMode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.split_coverMode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement.split_cover_sub_integer`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor](ThirdCoverIntegerFactor.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro](ThirdCoverVirasoro.md)
