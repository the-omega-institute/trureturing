# Hodge Frame

## Abstract

Hodge Frame

Hodge–Tate maps of distinct weights are independent; jumps read from a basis of them. Breuil–Kisin ring W[[z]] inside A_inf: definition, Frobenius, coordinates, Weierstrass division. Hodge frame: invariant B_dR basis adapted to filtration, giving de Rham implies Hodge–Tate.

**Theorem 1.1 (exists_hodge_frame).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/HodgeFrame.exists_hodge_frame`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/HodgeFrame.exists_hodge_frame` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Hodge frame: let j have open image, F be coarser than the near-1 filter, U in GL(B_dR) with N(g)·gU = U for F-almost all g, N(g) over Q̄_p. Then UY = W·diag(t^k_i), again invariant, with W in GL(B_dR^+) and Y in SL(Z̄_p) fixed for F-almost all g.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/HodgeFrame.exists_hodge_frame`
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/TateSen/DeRhamFiltration](../TateSen/DeRhamFiltration.md)
