# The crown auxiliary Chebyshev identity

## Abstract

The weighted auxiliary polynomial is a shifted Chebyshev quotient.

This polynomial identity is a repository-derived ingredient for the log-concavity argument. It concerns the auxiliary polynomial, not the actual f-polynomial discussed in source Remark 3.8.

**Theorem 1.1 (The exact identity for every n).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeChebyshev.crownAuxiliaryPolynomial_chebyshev`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeChebyshev.crownAuxiliaryPolynomial_chebyshev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every natural n, X times Q_n equals twice T_n((X+2)/2) minus two, as an identity of rational polynomials. Q_n is the sum of A(n,m)X^(m-1) over 1 <= m <= n. The identity is proved through its coefficients and the Chebyshev recurrence, including n equals zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeChebyshev.crownAuxiliaryPolynomial_chebyshev`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeScalar](CrownOrderPolytopeScalar.md)
