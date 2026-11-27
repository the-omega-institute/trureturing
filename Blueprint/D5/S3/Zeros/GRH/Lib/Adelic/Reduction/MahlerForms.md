# Mahler Forms

## Abstract

Mahler Forms

Field elements with bounded denominators and very small conjugates vanish. Compactness in adelic GL_n from determinant bound; reduced bases in a compact set. Mahler-Godement criterion core: dual reduced bases have finitely many Gram matrices, form varying.

**Theorem 1.1 (exists_finite_gram).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Adelic/Reduction/MahlerForms.exists_finite_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Adelic/Reduction/MahlerForms.exists_finite_gram` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For compact K ⊂ GL_n(𝔸) there are finite F, compact C: if y*Jy ∈ K, some Y ∈ GL_n(E), d ∈ E^n have (Y*JY)_{ij} = 0 when d_i, d_j ≠ 1, ((W⁻¹y)_f, y⁻¹Z) ∈ C, (d, Z*JZ) ∈ F, for W = (Y*J)⁻¹, Z = W·diag d.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Adelic/Reduction/MahlerForms.exists_finite_gram`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Reduction/MinkowskiSecond](MinkowskiSecond.md)
