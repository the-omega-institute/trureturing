# Tensor Powers

## Abstract

Tensor Powers

Projective embeddings by linear systems: properness, closed immersions, Segre, affine charts. Tensor products and powers of line bundles; Segre and Veronese embeddings.

**Theorem 1.1 (isProjEmbedding_pi).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/Geometry/TensorPowers.isProjEmbedding_pi`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/Geometry/TensorPowers.isProjEmbedding_pi` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Segre: let W be proper over S, with finitely many S-maps π_l: W → Z_l that jointly separate morphisms into W over S. If each N_l satisfies LineBundle.IsProjEmbedding on Z_l, so does the Segre product of the π_l^*N_l on W.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/Geometry/TensorPowers.isProjEmbedding_pi`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Geometry/ProjectiveSpace](ProjectiveSpace.md)
