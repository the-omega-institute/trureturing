# Valued Matrix

## Abstract

Valued Matrix

Polynomials in matrices: adjoints, base change, invertibility, characteristic polynomial divisibility. Diagonalisation with simple roots; Sylvester's law of inertia. Valuation bounds for matrix products; GL_n(O) as integral entries with unit determinant.

**Theorem 1.1 (mem_intGL_iff_det).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ValuedMatrix.mem_intGL_iff_det`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ValuedMatrix.mem_intGL_iff_det` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Over a field F with a valuation v into the value group ℤᵐ⁰, an invertible matrix g lies in GL_n(𝒪_F) if and only if all its entries have valuation at most 1 and v(det g) = 1.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ValuedMatrix.mem_intGL_iff_det`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Groups/ValuationPair](../Groups/ValuationPair.md)
