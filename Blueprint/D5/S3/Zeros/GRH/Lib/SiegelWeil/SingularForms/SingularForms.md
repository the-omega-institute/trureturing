# Singular Forms

## Abstract

Singular Forms

Adapted hyperbolic splittings compose, reindex and factor in stages. Coefficient at a degenerate index; definition of invariance under the radical at split places. Fourier expansion along a larger isotropic space; coefficient vanishes with singular-index ones. Singular forms: coefficients vanish if unimodular ones do, by induction on lattice index.

**Theorem 1.1 (freitag).**

Lean statement: `D5/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/SingularForms.freitag`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/SingularForms.freitag` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

After Freitag: let f be automorphic, fixed by integral points on S, with Space.Splitting.RadicalInvariant along an extra line; det T ≠ 0. If its T-coefficient vanishes at points acting on the frame by γ on S with δ⁻¹γᴴTγ unimodular, it vanishes at all points supported on S ∪ S̄.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/SingularForms.freitag`
- Dependency: [D5/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/AdaptedHom](AdaptedHom.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/DualPair/PairSumNegation](../../Weil/DualPair/PairSumNegation.md)
