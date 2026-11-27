# Local Components

## Abstract

Local Components

Principal congruence subgroups form a neighbourhood basis of 1 in finite adelic GL_n. Local components of finite adelic unitary group; GL_n at split places; restricted product API.

**Theorem 1.1 (range_atSplit).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Adelic/Adeles/LocalComponents.range_atSplit`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Adelic/Adeles/LocalComponents.range_atSplit` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For a split finite place w (w̄ ≠ w), the image of atSplit : GL_n(E_w) → G_f is the subgroup of elements with component 1 at every place other than w and w̄.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Adelic/Adeles/LocalComponents.range_atSplit`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdeleIdempotent](AdeleIdempotent.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Unitary/SpaceDefs](../Unitary/SpaceDefs.md)
