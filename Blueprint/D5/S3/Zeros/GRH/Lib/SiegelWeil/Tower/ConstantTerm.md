# Constant Term

## Abstract

Constant Term

Constant term of a theta integral along an isotropic line, unfolded over orbits.

**Theorem 1.1 (exists_unfold_constant_term).**

Lean statement: `D5/S3/Zeros/GRH/Lib/SiegelWeil/Tower/ConstantTerm.exists_unfold_constant_term`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/SiegelWeil/Tower/ConstantTerm.exists_unfold_constant_term` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Unfolding: for some real c ≠ 0, if the term x = 0 vanishes, ∫_{[U(V′)]} Σ_x constTermAt x (ω(g,h)f) dh is c times the integral of |t|^(rk V+1) Σ_{ξ∈E^×} θ(lineTerm) over ideles mod E^×, [U(V)] and the maximal compact subgroup, when this integrand is integrable.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/SiegelWeil/Tower/ConstantTerm.exists_unfold_constant_term`
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/DualPair/ThetaIntegralLaws](../../Weil/DualPair/ThetaIntegralLaws.md)
