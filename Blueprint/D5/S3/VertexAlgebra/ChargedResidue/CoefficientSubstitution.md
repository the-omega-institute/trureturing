# CoefficientSubstitution

## Abstract

Formal collision residue coefficients.

**Theorem 1.1 (Coefficient substitution with the Jacobian).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/CoefficientSubstitution.coeff_subst_jacobian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/CoefficientSubstitution.coeff_subst_jacobian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every complex formal power series f, unit u and natural coefficient n, the nth coefficient of f(X*u) times u^(-(n+1)) times the formal derivative of X*u equals the nth coefficient of f. The proof splits off the constant term and cancels its positive-degree contribution using the derivative of an inverse unit power. It includes n=0 and imposes no polynomial or support restriction on f.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/CoefficientSubstitution.coeff_subst_jacobian`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/JointDiagonal](JointDiagonal.md)
