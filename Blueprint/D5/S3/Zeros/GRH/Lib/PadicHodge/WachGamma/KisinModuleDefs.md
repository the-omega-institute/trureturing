# Kisin Module Defs

## Abstract

Kisin Module Defs

the Artin–Schreier–Witt resolution over the tilt. This file treats only the φ−1 step of Herr's complex, on Witt vectors of the tilt of C_p modulo p^m, and not the Γ-step. Source: L. Herr, Sur la cohomologie galoisienne des corps p-adiques, Bull. SMF 126 (1998) 563–600.

**Theorem 1.1 (smallPart_spec).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/KisinModuleDefs.smallPart_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/KisinModuleDefs.smallPart_spec` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let S be the image of W(𝔪^♭) in M=W(C^♭)⊗ℤ/p^m(1). Then p^m kills M, φ−1 is onto, φd−d∈S implies d∈ℤ/p^m(1)+S, S∩ℤ/p^m(1)=0; and for ρ trivial modulo p^m near 1, L: W(C^♭)⊗ρ→M linear and any v, L(hv−v)∈S for h near 1.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/KisinModuleDefs.smallPart_spec`
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/Herr/GaloisLattices](../Herr/GaloisLattices.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/DeRhamValues](../WachKisin/DeRhamValues.md)
