# Local Embedding

## Abstract

Local Embedding

Local conditions: unramified or crystalline, finite type, killing polynomials, jumps. Decomposition group versus local Galois group: Frobenius, inertia, cyclotomic character agree.

**Theorem 1.1 (isFrob_iff).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GaloisRep/Main/LocalEmbedding.isFrob_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GaloisRep/Main/LocalEmbedding.isFrob_iff` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For s in the decomposition group of A and j = h.toGp, the map to Gal(ℚ̄_ℓ/ℚ_ℓ): j(s) induces x ↦ x^q on the residue field of ℚ̄_ℓ if and only if s induces x ↦ x^q on that of A.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GaloisRep/Main/LocalEmbedding.isFrob_iff`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Places/PadicDecomposition](../../ClassField/Places/PadicDecomposition.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/Defs](../../PadicHodge/Crystalline/Defs.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Unramified/SphericalHecke](../../Weil/Unramified/SphericalHecke.md)
