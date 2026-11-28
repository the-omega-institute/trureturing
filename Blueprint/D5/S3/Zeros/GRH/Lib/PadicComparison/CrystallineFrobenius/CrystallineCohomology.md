# Crystalline Cohomology

## Abstract

Crystalline Cohomology

p-adic etale cohomology of smooth proper varieties is finite with continuous Galois action. Natural Galois-equivariant period map, bijective for smooth proper varieties. Frobenius relations on special-fibre points pass to l-adic cohomology; inertia acts trivially. p-adic cohomology is crystalline and its Frobenius satisfies the congruence relation.

**Theorem 1.1 (isCrystalline_and_linearFrob_rel).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicComparison/CrystallineFrobenius/CrystallineCohomology.isCrystalline_and_linearFrob_rel`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicComparison/CrystallineFrobenius/CrystallineCohomology.isCrystalline_and_linearFrob_rel` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

R noetherian, mapping into the place A above p of Ω ≅ ℚ̄; W, Y proper over R, charted over Ω, Y also over R; (γ_i, a_i) Weil pairs at A. If ∑ m_i[Frob^{a_i}u_i(x)] = 0 at field points x of W above A, then V^n(Y) is crystalline and ∑ m_i u_i^*β_{γ_i,a_i} = 0.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicComparison/CrystallineFrobenius/CrystallineCohomology.isCrystalline_and_linearFrob_rel`
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/CrystallineClasses](../Crystalline/CrystallineClasses.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/CrystallineFrobenius/DenseRelation](DenseRelation.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/GaloisWeight](../HodgeTate/GaloisWeight.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/PrimitiveComparison](../Primitive/PrimitiveComparison.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/RegularityFrobenius](../../PadicHodge/Crystalline/RegularityFrobenius.md)
