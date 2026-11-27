# Decomposition Local

## Abstract

Decomposition Local

Places from p-adic embeddings; decomposition group is Galois group of the completion. Decomposition field is local; normalised valuation; index equals e·f in towers.

**Theorem 1.1 (ramification_in_tower).**

Lean statement: `D5/S3/Zeros/GRH/Lib/ClassField/Places/DecompositionLocal.ramification_in_tower`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/ClassField/Places/DecompositionLocal.ramification_in_tower` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let U ≤ Γ be open, with field L, and A lie over v and w, of ramification index e, residue degree f. Then [Dec(A) : U ∩ Dec(A)] = ef; Ine(A) ≤ U gives e = 1; Dec(A) ≤ U gives q_w = q_v, ord_L = ord_K.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/ClassField/Places/DecompositionLocal.ramification_in_tower`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Places/FrobeniusOnRoots](FrobeniusOnRoots.md)
