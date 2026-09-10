# Motzkin Theorem 4 clause refutation

## Abstract

The printed clause H_{12n+7}(F(x,4)) = -64(n+1)^2 of Theorem 4 in arXiv:2502.21050v1 fails at n = 0, where the Hankel determinant is plus 64.

Wang and Zhang, Hankel determinants for convolution powers of Motzkin numbers, arXiv:2502.21050v1, Theorem 4 on printed page 3, states twelve clauses for F(x,4) with no restriction on n. This module refutes exactly one of them, the H_{12n+7} clause, and only through the instance n = 0. It does not claim that the authors' intended proposition is false, and it does not claim that their proof has a gap; a single numerical instance cannot establish either.

Eleven of the twelve printed clauses were recomputed at n = 0 by two independent exact algorithms with independently generated coefficients, and all eleven agree with the paper. Only index seven disagrees. That distribution is the positive control for the computation itself: an error in the Motzkin sequence, the convolution or the determinant would move every clause, not exactly one. It also indicates a typographical sign error rather than a mathematical one, but the corrected formula is not formalised here for general n.

**Theorem 1.1 (The printed H_{12n+7} clause is false).**

Lean statement: `D5/S0/Certificates/MotzkinTheoremFourRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/MotzkinTheoremFourRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Motzkin sequence, its Cauchy convolution powers and the Hankel determinant are reused from the already frozen sibling module. The determinant is obtained from an integer matrix product identity and triangular determinant formulas rather than a direct expansion. The counterexample value is attested inside the source itself: section 3.2 on printed page 7 gives equation (6) and the initial values from which the same H_7 follows. The refutation judgment is derived here; no priority is claimed, and no separate erratum was found in the searched scope.

## References

- Truth anchor: `D5/S0/Certificates/MotzkinTheoremFourRefutation.result`
- Dependency: [D5/S0/Certificates/MotzkinConvolutionHankelRefutation](MotzkinConvolutionHankelRefutation.md)
