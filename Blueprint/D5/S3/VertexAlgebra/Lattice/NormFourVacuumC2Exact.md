# Exact Dimension of the Norm-Four Vacuum C2 Quotient

## Abstract

The literal C2 quotient of the actual norm-four vacuum algebra has complex dimension three.

Let D be a finite integral symmetric lattice with even diagonal, a a charge with B(a,a)=4, and s a complex number with s squared equal to one. Write S for the complex span of all finite negative words in the actual Virasoro modes L_m on the vacuum. Its literal C2 subspace is the span of u_(-2)v with both u and v in S. Let C be its inverse image under the inclusion of S into the ambient lattice carrier.

**Theorem 1.1 (Finite-dimensional quotient of dimension three).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Exact.actual_vacuum_c2_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Exact.actual_vacuum_c2_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,a,s satisfying precisely these hypotheses, the quotient S/C is finite dimensional over the complex numbers and its finrank is exactly three. The classes of the vacuum, L_(-2) applied to the vacuum, and L_(-2) squared applied to the vacuum form a basis.

Bilinearity expands C2 as the span of products of two negative words. Each product is an actual L_0 eigenvector of weight equal to the sum of its word weights plus one. Finite decomposition and polynomial projection onto L_0 eigenvalues isolate the homogeneous C2 fibers. The fibers of weights zero and two vanish. Weight-one words vanish, weight-three words lie in the span of L_(-3) applied to the vacuum, and translation shows that the weight-four C2 fiber lies in the span of d=L_(-4) applied to the vacuum.

Put b=L_(-2) squared applied to the vacuum. The actual Virasoro commutator gives L_4 d=(5/2) times the vacuum, L_4 b=(3/2) times the vacuum, L_2 squared d=(3/2) times the vacuum, and L_2 squared b=(17/8) times the vacuum. Hence A=(5/2)L_2 squared-(3/2)L_4 annihilates d and sends b to (49/16) times the nonzero vacuum. The weight-zero, weight-two and weight-four components therefore force every coefficient of a C2 relation among the three displayed classes to vanish. Their linear independence gives the lower bound three; the spanning theorem for the same literal quotient supplies finite dimensionality and the upper bound three.

The classical context is the simple Virasoro vacuum algebra at central charge one half and its C2 algebra; Li's Abelianizing vertex algebras provides the C2 framework. The norm-four vector retains its Dong-Mason-Zhu and Shimakura attribution. The proof assumes no PBW basis, positivity, rootlessness or independence of negative words. The dimension statement alone does not establish rationality, fusion, analytic CFT or string realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Exact.actual_vacuum_c2_dimension`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2](NormFourVacuumC2.md)
