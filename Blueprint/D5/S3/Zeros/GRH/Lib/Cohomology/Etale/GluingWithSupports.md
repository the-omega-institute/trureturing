# Gluing With Supports

## Abstract

Gluing With Supports

Compatible classes with supports glue when lower degrees vanish.

**Theorem 1.1 (exists_glued_class).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/GluingWithSupports.exists_glued_class`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/GluingWithSupports.exists_glued_class` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Gluing: let finitely many W_i ⊂ V lie in an intersection-closed class whose members A have H^n(A, U ∩ A) = 0 for n < d, with U ∪ ⋃ W_i dense. Then classes in H^d(W_i, U ∩ W_i) agreeing on overlaps come from H^d(V,U).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/GluingWithSupports.exists_glued_class`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Etale/RelativeChains](RelativeChains.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Geometry/OpenSubfunctors](../../General/Geometry/OpenSubfunctors.md)
