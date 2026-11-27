# Partitions

## Abstract

Partitions

Dense subfunctors form a Grothendieck topology; Mayer–Vietoris short exact sequence. Composition of pull-backs; an equivalence can be checked over a dense subfunctor. Idempotent partitions and Zariski-local subfunctors are dense for additive coefficients on comparable rings.

**Theorem 1.1 (hasZariskiDescent).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Partitions.hasZariskiDescent`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Partitions.hasZariskiDescent` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let F satisfy HasPartitions for ι and let η: ι → κ be injective. If any a, b ∈ κ(A) have an idempotent e ∈ ι(A) with a ∣ η(e)b and b ∣ (1 − η(e))a, then F satisfies Zariski descent HasZariskiDescent for κ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Partitions.hasZariskiDescent`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Etale/BijectiveComparisons](BijectiveComparisons.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Geometry/LocalTerms](../../General/Geometry/LocalTerms.md)
