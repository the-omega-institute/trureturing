# Finite Dimension of the Actual Norm-Four Zhu Quotient

## Abstract

Finite Dimension of the Actual Norm-Four Zhu Quotient.

**Definition 1.1 (Actual homogeneous circle product).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.circle`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.circle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a lattice D, natural weight n and actual states u,v, circle is the entire sum over j from zero through n of binomial(n,j) times u_(j-2)v.

**Definition 1.2 (Literal O-space).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.zhuO`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.zhuO` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every lattice D, charge a and complex s, let S be the actual negative-axis-word vacuum span. The O-space is the ambient complex span of all circle(n,u,v) with u,v in S and actual axis L0(u)=n u. Both arguments stay in S; the definition uses the actual eigenvalue equation.

**Theorem 1.3 (Actual finite additive quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.actual_zhu_quotient_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.actual_zhu_quotient_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite integral symmetric even-diagonal lattice D, charge a with B(a,a)=4, and complex s with s squared equal to one, literal O is contained in S and the existing additive quotient of S by the inverse image of O is finite dimensional over the complex numbers, with dimension at most three. No determinant invertibility or rank specialization is required.

The actual C2 homogeneous pair decomposition and its three representatives are reused. Finite eigenvalue separation extracts a single homogeneous component of the C2-plus-representatives decomposition. For a pair of grade N, its minus-two product equals the full circle product minus terms of strictly smaller grade. Strong induction on grade places every actual vacuum descendant in O plus the span of the vacuum, axis and its minus-one square.

Finite spanning of the literal additive quotient follows without a multiplication premise or an independence premise. This is the classical C2-to-Zhu finite filtration argument in the actual lattice carrier, following Zhu's associative algebra construction. The norm-four vector retains its Dong-Mason-Zhu and Shimakura attribution. The complex multiplication and cubic presentation are the subject of NormFourZhuAlgebra.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.actual_zhu_quotient_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.circle`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.zhuO`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Exact](NormFourVacuumC2Exact.md)
