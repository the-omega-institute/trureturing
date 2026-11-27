# Section Lifts

## Abstract

Section Lifts

Quasi-finiteness from ample pull-backs; identities for the pairing: ⟨x+y, z⟩ + ⟨x−y, z⟩ = 2⟨x, z⟩, ⟨mx, y⟩ = m⟨x, y⟩ for natural m, symmetry, and compatibility with additive maps; [m]*L = L^(m²). Maps on sections induced by isomorphisms of pulled-back line bundles; composition, uniqueness.

**Theorem 1.1 (comp).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/ThetaGroup/SectionLifts.comp`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/ThetaGroup/SectionLifts.comp` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Lifts compose: if Φ: H⁰(L) → H⁰(L') is pull-back along f followed by an isomorphism f^*L ≅ L', and Θ: H⁰(L') → H⁰(L'') likewise along g, then Θ∘Φ is such a map along f∘g: X'' → X.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/ThetaGroup/SectionLifts.comp`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Etale/TestRings](../../Cohomology/Etale/TestRings.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Geometry/ConstantFunctions](../../General/Geometry/ConstantFunctions.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/GroupBaseChange](../IntegralModel/GroupBaseChange.md)
