# QuadraticResidue

## Abstract

Formal collision residue coefficients.

**Theorem 1.1 (The actual collision coefficients include the Jacobian).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/QuadraticResidue.collision_scalar_jacobian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/QuadraticResidue.collision_scalar_jacobian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all signed integers a and B and natural N, collisionScalar is transported under h=X*(2+X). Every signed half exponent becomes its integer exponent; the normalized collision unit becomes (2+X)/2. The coefficient formula retains the inverse (N+1)st power of 2+X and the exact derivative 2*(1+X).

**Theorem 1.2 (Normalized collision residue in the quadratic coordinate).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/QuadraticResidue.collision_scalar_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/QuadraticResidue.collision_scalar_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Combining the Jacobian with the coordinate unit gives collisionScalar(a,B,N)=2^(2*B+1) times the Nth coefficient of (1+X)^(a+1)*(2+X)^(-2*B-N-1). Integer exponents are represented by the existing binomial series and actual unit powers. This is a coefficient identity and does not by itself prove the full physical forward law.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/QuadraticResidue.collision_scalar_coordinate`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/QuadraticResidue.collision_scalar_jacobian`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/CoefficientSubstitution](CoefficientSubstitution.md)
