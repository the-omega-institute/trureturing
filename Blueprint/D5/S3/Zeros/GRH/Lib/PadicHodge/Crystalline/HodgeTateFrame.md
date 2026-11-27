# Hodge Tate Frame

## Abstract

Hodge Tate Frame

Base change of a bilinear pairing and its naturality. Admissibility passes to cyclotomic twists, subgroups, images; basic rules of the period action. Potentially crystalline representations are Hodge–Tate: frame over C_p and rank-many jumps.

**Theorem 1.1 (exists_hasJumps).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/HodgeTateFrame.exists_hasJumps`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/HodgeTateFrame.exists_hasJumps` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let j have open image, R be algebraic over Z_p, and T be finite free over R and potentially crystalline. Then at each γ: R → C_p the jumps of T, with multiplicity, form a multiset of cardinality the rank of T.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/HodgeTateFrame.exists_hasJumps`
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/HodgeFrame](../WachKisin/HodgeFrame.md)
