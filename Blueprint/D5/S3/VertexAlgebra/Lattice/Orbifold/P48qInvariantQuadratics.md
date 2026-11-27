# Fixed Weight-Two States in the Untwisted P48q Lattice

## Abstract

The quadratic states of complementary invariant Cartan blocks give two linearly independent fixed vectors in weight two of the untwisted P48q lattice carrier.

Let D be lattice data whose real Gram matrix is positive definite, and write B for the rational extension of its Gram pairing. For a rational Cartan subspace W, choose a basis of W and its dual for the restricted Gram form. The quadratic state of W is one half of the sum of the minus-one mode products of the corresponding pairs of currents. This is the block version of the inverse-form quadratic construction in Bakalov–Kac, Section 4.1, equation (4.16) of arXiv:math/0402315v1.

**Theorem 1.1 (Mode one fixes the currents in the block).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.blockQuadratic_mode_one_of_mem`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.blockQuadratic_mode_one_of_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every direction x in W, mode one of its block quadratic acts as the identity on the current of x. The two contractions of the quadratic with that current reconstruct x from its basis and dual basis coordinates. The factor of one half cancels the two copies.

**Theorem 1.2 (Mode one kills the perpendicular currents).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.blockQuadratic_mode_one_of_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.blockQuadratic_mode_one_of_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every rational direction perpendicular to W, mode one of the quadratic state of W sends its current to zero. All contractions vanish because the basis and dual basis vectors lie in W.

**Theorem 1.3 (Independent fixed quadratics from invariant blocks).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.invariant_block_quadratics`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.invariant_block_quadratics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let a group act on the rational Cartan space preserving B. Let its complex representation on the lattice carrier intertwine the rational currents and preserve all mode products. For every nonzero proper invariant subspace W, the quadratic states of W and its B-orthogonal complement have weight two, are fixed by the group, and are linearly independent over ℂ.

The orthogonal complement is invariant because the Cartan action preserves B. Each action transports a basis and its Gram-dual basis together, and the quadratic sum is basis independent. The minus-one product of two weight-one currents has weight two. Mode one on a nonzero current from each block distinguishes the two states.

**Theorem 1.4 (Two fixed weight-two states for P48q).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.p48q_prime_to_three_fixed_weight_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.p48q_prime_to_three_fixed_weight_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let H ≤ SL₂(F₄₇) have order prime to three and act faithfully on the rational P48q Cartan space preserving its Gram form. Suppose its complex representation on the untwisted lattice carrier intertwines the rational currents and preserves all mode products. There are two complex-linearly independent states of weight two fixed by every element of H. The rank-48 rational reducibility theorem supplies the nonzero proper invariant block, and the certified positive definite Gram matrix gives its complementary block.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.blockQuadratic_mode_one_of_mem`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.blockQuadratic_mode_one_of_orthogonal`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.invariant_block_quadratics`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.p48q_prime_to_three_fixed_weight_two`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport](../Automorphisms/ConformalGroundTransport.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity](P48qGramPositivity.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility](P48qPrimeToThreeReducibility.md)
