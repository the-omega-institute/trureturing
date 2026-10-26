# The Actual Simple Graded Vacuum Vertex Algebra

## Abstract

The actual norm-four cyclic vacuum space is a simple naturally graded state-field vertex algebra.

Let D be a finite integral symmetric lattice with even diagonal, a a charge with B(a,a)=4, and s a complex number with s squared equal to one. Let S be the actual complex span in Carrier D of all negative words L_(-(k+1)) on the vacuum, for natural k, where L_m is the coefficient Y(e)_(m+1) of the norm-four lattice state e.

**Definition 1.1 (The restricted state-field algebra).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra.vertexAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra.vertexAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every such D,a,s, vertexAlgebra is a StateFieldVertexAlgebra on S. Its field coefficients and translation are the restrictions of the actual lattice fields and translation. The fields are genuine Hahn-module series with inherited well-founded support. The structure contains the vacuum field, creation, creativity, translation of the vacuum, covariance, uniform locality and the full integer Borcherds identity, including finite support of its left, first and second families.

**Definition 1.2 (Natural word grades).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra.grade`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra.grade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,a,s and natural n, grade n is the submodule of S whose ambient vectors lie in the span of words of total grade n. A word with entries k_1 through k_r has total grade the sum of k_i+1; the empty word has grade zero. No independence, nonvanishing or ordering of the word vectors is assumed.

**Theorem 1.3 (Embedding, central charge, grading and simplicity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra.actual_simple_graded_vacuum_vertex_algebra`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra.actual_simple_graded_vacuum_vertex_algebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,a,s under precisely the hypotheses above, write V for vertexAlgebra. Its vacuum includes as the actual nonzero lattice vacuum. For every v in S, inclusion takes V.translation v to the ambient translation of v, and V.translation v equals restricted L_(-1) v. For every u,v in S and integer k, inclusion takes the k-th coefficient of V.stateField u on v to the actual ambient coefficient Y(u)_k v, which belongs to S.

There exists e in S that includes as the actual norm-four state and lies in grade two. For every integer m its coefficient at m+1 is restricted L_m. For all integers m,n, the commutator is (m-n)L_(m+n) plus delta_(m+n,0)(m cubed minus m)/24 times the identity. Its self-products at indices zero, one, two and three are respectively translation of e, twice e, zero and one quarter of the vacuum; every self-product at integer k at least four vanishes.

Grade zero is exactly the vacuum line and every natural grade is finite dimensional. Every v in S is the sum of a finitely supported family f with f(n) in grade n. Any such homogeneous family summing to zero is zero. Restricted L_0 acts on grade n by the scalar n. For u in grade n, v in grade t and any integer k, put w=n+t-k-1. If w is nonnegative, the coefficient u_k v belongs to grade w.toNat; if w is negative, that coefficient is zero. Every complex submodule of S invariant under all coefficients u_k for all u in S and integers k is zero or all of S.

Closure follows by induction on the left word using both finite sums in the actual iterate identity, then by linear span induction. Translation equals L_(-1) on this cyclic span. Finitely many compositions enumerate each word grade, without a PBW or basis assertion. The finite spectral projector separates the homogeneous components. The actual L_0 commutator and the derivative-state identity give coefficient weights, and the absence of negative natural weights forces negative-weight coefficients to vanish. Coefficient invariance implies invariance under every actual L_m, so cyclic irreducibility proves simplicity.

The norm-four state retains its Dong-Mason-Zhu and Shimakura attribution; the lattice and residue calculus retain their Bakalov-Kac, Carnahan and Matsuo-Nagatomo attribution. No positivity, rootlessness, unitarity, abstract minimal-model identification or simplicity premise is used. This result supplies an algebraic vacuum state-field algebra; analytic CFT, fusion, anomalies, Monster moonshine and string or AdS-CFT realization require further results.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra.actual_simple_graded_vacuum_vertex_algebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra.grade`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra.vertexAlgebra`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVacuumIrreducible](NormFourVacuumIrreducible.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualVertexAlgebra](../LatticeActualVertexAlgebra.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeEnergyGrading](../LatticeEnergyGrading.md)
