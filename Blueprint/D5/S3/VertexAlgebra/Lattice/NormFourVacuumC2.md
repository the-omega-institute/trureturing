# C2-Cofiniteness of the Actual Norm-Four Vacuum Algebra

## Abstract

The actual norm-four cyclic vacuum vertex algebra has a C2 quotient of dimension at most three.

Let D be a finite integral symmetric lattice with even diagonal, a a charge with B(a,a)=4, and s a complex number with s squared equal to one. Write S for the actual complex span in Carrier D of all finite negative words in the modes L_m=Y(e)_(m+1) on the vacuum, where e is the norm-four state. The actual restricted state-field algebra on S is simple and naturally graded.

**Definition 1.1 (The literal C2 subspace).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2.C2`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2.C2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C2(D,a,s) is the ambient complex linear span of the actual products u_(-2)v, with both u and v in the same vacuum space S. The coefficient is that of the actual lattice state-field map, rather than an independently prescribed operation.

**Theorem 1.2 (Finite-dimensional quotient with upper bound three).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2.actual_vacuum_c2_cofinite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2.actual_vacuum_c2_cofinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,a,s with exactly the hypotheses above, C2(D,a,s) is contained in S. Let C be its inverse image under the inclusion of S into Carrier D. The quotient S/C is finite dimensional over the complex numbers, and its finrank is at most three.

Translating the left state in an actual product shows that every coefficient u_(-r-2)v, for natural r and u,v in S, belongs to C2. The all-integer mode commutator at indices -1 and -2 proves that L_(-2) preserves C2: every correction coefficient has index -3-j, for natural j, and the correction sum has finite support. The actual level-six null relation then places L_(-2) cubed applied to the vacuum in C2.

Induction on arbitrary finite negative words reduces every vector modulo C2 to the span of the vacuum, L_(-2) applied to the vacuum, and L_(-2) squared applied to the vacuum. The L_(-1) step uses its equality with translation on S. The three quotient classes span, which proves both finite dimensionality and the bound. No PBW basis, independence of these three classes, positivity, rootlessness or rationality assumption is used.

Li's Abelianizing vertex algebras, Corollary 3.6 and Proposition 3.7, provide classical C2 context. The norm-four construction retains its Dong-Mason-Zhu and Shimakura attribution. The conclusion is an upper bound; dimension equality, rationality, fusion, analytic CFT, Monster moonshine and string realization require further results.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2.C2`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2.actual_vacuum_c2_cofinite`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra](NormFourVacuumVertexAlgebra.md)
