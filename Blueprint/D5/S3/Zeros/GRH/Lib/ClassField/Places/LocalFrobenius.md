# Local Frobenius

## Abstract

Local Frobenius

Uniformisers and the normalised rational valuation on the algebraic closure of a local field. Frobenius exists and, with inertia, topologically generates a local Galois group.

**Theorem 1.1 (frobenius_spec).**

Lean statement: `D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalFrobenius.frobenius_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalFrobenius.frobenius_spec` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let Γ = Gal(Ω/K) be the absolute Galois group of a henselian local field, with valuation ring A of Ω. An arithmetic Frobenius exists; for any such φ the products φ^n·i (n ≥ 0, i in inertia) are dense in Γ; A is integral over A ∩ K.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalFrobenius.frobenius_spec`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Places/Places](Places.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Groups/ArtinDefs](../../General/Groups/ArtinDefs.md)
