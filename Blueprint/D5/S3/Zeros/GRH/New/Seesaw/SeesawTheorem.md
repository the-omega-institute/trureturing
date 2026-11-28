# Seesaw Theorem

## Abstract

Seesaw Theorem

Seesaw identity for the chain of lifts, by downward induction with finite cuts.

**Theorem 1.1 (seesaw).**

Lean statement: `D5/S3/Zeros/GRH/New/Seesaw/SeesawTheorem.seesaw`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Seesaw/SeesawTheorem.seesaw` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

The seesaw identity: there is a non-zero complex number c such that for every twist ϑ some good datum Ψ (Data.IsGoodDatum) has ι(𝒫(cφ)) = B^Ψ φ for all ramified columns φ; 𝒫 is the Poincaré series, ι = Data.ι the chain of m theta lifts through the spaces Y_j, and B^Ψ = Data.Bμ the chain through the definite spaces X_j with finite datum Ψ, restricted to Y_m.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Seesaw/SeesawTheorem.seesaw`
- Dependency: [D5/S3/Zeros/GRH/New/Filling/FillingTheorem](../Filling/FillingTheorem.md)
