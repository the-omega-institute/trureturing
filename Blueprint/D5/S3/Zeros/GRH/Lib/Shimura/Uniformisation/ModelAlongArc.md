# Model Along Arc

## Abstract

Model Along Arc

Linear maps to the torsion module come from finite-adelic matrices. Objects modelled on theta tori: uniformisation, torsion points, Weil pairing, multiplier. Isogenies of modelled PEL abelian varieties correspond to rational matrices. Analytic families of period maps; theta coordinates vary holomorphically after scaling. Uniformisation of the generic fibre extends over a valuation ring by properness.

**Theorem 1.1 (exists_model_over_arc).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ModelAlongArc.exists_model_over_arc`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ModelAlongArc.exists_model_over_arc` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let y be an object over a valuation ring O with fraction field ℂ and x its generic fibre. A model of x on (g, ℓ) gives a model of y on (g, ℓ) whose sections π'(w) restrict to π(w) at the generic point.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ModelAlongArc.exists_model_over_arc`
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/Extension/ArcExtension](../Extension/ArcExtension.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/ThetaNormality/RiemannRelation](../ThetaNormality/RiemannRelation.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/AppellHumbert](AppellHumbert.md)
