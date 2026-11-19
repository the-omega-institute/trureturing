# Seventh-height actual singular factor cover

## Abstract

The actual integer pencil L₀Qᵢ−LᵢQ₀ has a root-relevant cover by at most three primitive irreducible integer factors under a single seventh-weight height gap. This replaces the old eighth-weight localized-quadratic branch by two proved estimates: actual quadratic pencils use their structural seventh-weight resultant theorem, and a quadratic factor of a genuine cubic uses the sixth-weight mixed resultant theorem. The cubic localized-factor branch and the finite factor-lifting construction are adapted from PascadiPrimeCubeSingularCover.actual_singular_factor_cover. The literal coefficient bounds, common root modulo p³, singularity modulo prime p, baseline L unit and nonzero polynomial reductions all remain explicit. This is an algebraic cover and does not assert a larger tuple-count exponent or the full arbitrary-modulus conjecture.

Two localized cubic factors are handled by the original actual residual. When both localized factors are quadratic, one genuine cubic original suffices for the mixed sixth-weight bound. If both originals are quadratic, the actual LQ quadratic elimination supplies the common factor, and the constant complementary factors together with their modular units transfer it to the localized factors. Nonzero singular quadratic reduction ensures that the actual quadratic leading coefficient is nonzero modulo p. No generic factor-height hypothesis replaces the actual LQ coefficient structure. The common factor chosen for every member belongs to the root-relevant factors of one fixed member.

**Theorem 1.1 (actual_seventh_height_singular_factor_cover).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiSeventhHeightCover.actual_seventh_height_singular_factor_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiSeventhHeightCover.actual_seventh_height_singular_factor_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For a family with literal bounds |lᵢ|≤3I, |mᵢ|≤3J, |qᵢ|≤I², |rᵢ|≤2IJ, |sᵢ|≤J², J≤I and J≥1, original polynomial height H≥1, a common root modulo p³, derivative zero modulo p, nonzero reductions, and a unit baseline L, the gap max(10368·3⁹, max(14256, 24(8H)⁴))(IJ)⁷<p⁵ gives a cover by at most three primitive irreducible integer factors of the selected original member. Every factor vanishes at the actual residue root and has nonzero reduction; every original member is divisible by one of them. The proof consumes both the actual quadratic resultant theorem and the improved true-cubic factor estimate.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSeventhHeightCover.actual_seventh_height_singular_factor_cover`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiActualQuadraticResultant](PascadiActualQuadraticResultant.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiCubicQuadraticHeight](PascadiCubicQuadraticHeight.md)
