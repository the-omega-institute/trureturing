# Drinfeld Lifting

## Abstract

Drinfeld Lifting

Linear functions on w-torsion with zero differential span at most n-1 dimensions. Absolute Frobenius of a scheme; pull-back of line bundles is a power. Drinfeld's lifting lemma for first-order deformations of the abelian object.

**Theorem 1.1 (drinfeld_lift).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/Deformation/DrinfeldLifting.drinfeld_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/Deformation/DrinfeldLifting.drinfeld_lift` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Drinfeld's lifting lemma. Let x, x' deform x₀ over k[ε], and let c in O_E kill all infinitesimal points of A_x'. Then some homomorphism F: A_x → A_x' reduces to c, and F(y) = c·y' whenever y and y' agree modulo ε.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/Deformation/DrinfeldLifting.drinfeld_lift`
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/CongruenceRelation/KernelReduction](../CongruenceRelation/KernelReduction.md)
