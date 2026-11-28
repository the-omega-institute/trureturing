# Siegel Weil Formula

## Abstract

Siegel Weil Formula

Siegel–Weil formula in the convergent range. Here a split space of rank 2p is paired with a hermitian space of rank above 2p, both unimodular at every finite place, over a CM field with the 5040th roots of unity. The Eisenstein series is a sum over Lagrangians, and the proof uses one Hecke operator at a split place against the positive Eisenstein series. Source: A. Weil, Sur la formule de Siegel dans la théorie des groupes classiques, Acta Math. 113 (1965), n° 52 Thm 5; method of proof after Andrianov (1979), Harris (1981), P. Garrett, The Siegel-Weil formula in the convergent range (notes, 2005).

**Theorem 1.1 (siegel_weil).**

Lean statement: `D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelWeilFormula.siegel_weil`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelWeilFormula.siegel_weil` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Siegel–Weil formula: for S split of rank 2p and rk T > 2p, the norms of the zero terms ev_L are summable over the Lagrangians L of S, and for every f, h ↦ θ(ω(1,h)f) is integrable on [U(T)] with mean ∑_L ev_L f.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelWeilFormula.siegel_weil`
- Dependency: [D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelSets](SiegelSets.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/MixedModel/EquivariantCoefficients](../../Weil/MixedModel/EquivariantCoefficients.md)
