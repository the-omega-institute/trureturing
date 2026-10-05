# Polynomial Fock Deformation Covariance

## Abstract

The actual polynomial substitution satisfies every Fock product coefficient law.

Let F=C[X_0,X_1,...] be the existing polynomial Fock space. Its product mu(u,r,v) is the actual normalized mode r of Y(u) acting on v. The independent variable q records inverse parameter powers; normalized mode r means Laurent power -r-1.

**Definition 1.1 (Independent generator substitution).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockDeformationCovariance.deformation`

*Formalization.* `D5/S3/VertexAlgebra/PolynomialFockDeformationCovariance.deformation` (`✓ std3`).

*Citation.* Haisheng Li (2010). *Twisted modules and pseudo-endomorphisms*. URL: <https://arxiv.org/abs/1004.0864v1>.

*Commentary.*

For every complex lambda, deformation(lambda) is the complex algebra homomorphism F to F[q] defined by MvPolynomial.aeval with X_j sent to the sum of the constant polynomial X_j and the degree j+1 monomial with coefficient MvPolynomial.C((-1)^j lambda). No product mu, covariance equation or defining recurrence enters this construction.

**Definition 1.2 (Actual polynomial coefficients).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockDeformationCovariance.deformationCoeff`

*Formalization.* `D5/S3/VertexAlgebra/PolynomialFockDeformationCovariance.deformationCoeff` (`✓ std3`).

*Citation.* Haisheng Li (2010). *Twisted modules and pseudo-endomorphisms*. URL: <https://arxiv.org/abs/1004.0864v1>.

*Commentary.*

For every complex lambda, every natural k and every p in F, deformationCoeff(lambda,k,p) is exactly Polynomial.coeff at k of deformation(lambda)(p).

**Theorem 1.3 (All charges, states, integer modes and natural coefficients).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockDeformationCovariance.deformation_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockDeformationCovariance.deformation_covariance` (`✓ std3`). ∎

*Citation.* Haisheng Li (2010). *Twisted modules and pseudo-endomorphisms*. URL: <https://arxiv.org/abs/1004.0864v1>.

*Commentary.*

For every complex lambda, all u,v in F, every integer r and every natural k, deformationCoeff(lambda,k,mu(u,r,v)) equals the sum over d in range(k+1) and e in range(k-d+1) of integerBinomial(-d,k-d-e) times mu(deformationCoeff(lambda,d,u),r+(k-d-e),deformationCoeff(lambda,e,v)), where integerBinomial is the existing integer generalized binomial cast to C. The first-state shift is k-d-e. There are no additional hypotheses, including at lambda=0 or k=0.

The Li reference supplies the classical translated-parameter convention. This concrete realization formula is not attributed as a literal published theorem, a compiled supplier or a novelty claim. It does not establish a charged-module Jacobi law, fusion, a Monster realization or a geometric string/AdS correspondence.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockDeformationCovariance.deformation`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockDeformationCovariance.deformationCoeff`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockDeformationCovariance.deformation_covariance`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockJacobi](PolynomialFockJacobi.md)
