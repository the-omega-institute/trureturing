# Coefficients of the normalized signed cycles

## Abstract

Unit coefficients in normalized top integral cycles of the signed fair-bias complex.

**Theorem 1.1 (Each oriented face has coefficient zero, one, or minus one).**

Lean statement: `D5/S3/TotalVariation/FairBiasCycleCoefficients.normalized_cycle_unit_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasCycleCoefficients.normalized_cycle_unit_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite binary column family and an order on its signed labels. Take an integral cycle supported on the signed facets. Its coordinates on the full-restriction facets are one at the selected facet and zero elsewhere.

Call a member of a basis passive when a smaller element can replace it. At a basis with a nonpassive element, use the boundary equation on the ridge opposite the least such element. Its other cofaces come later and the exchange preserves passivity and makes the inserted element passive.

Work backwards through the facet order. At a nonzero coefficient all elements outside the selected facet are nonpassive. A missing element of the selected facet exceeds any lower bound strictly below every nonpassive element. At any nonzero later coface the removed element therefore lies outside the selected facet and the inserted element lies in it.

The fundamental circuit of each admissible inserted element lies in the common part of the current and selected bases together with the removed and inserted elements. After contraction of the common part, two such insertions would be parallel, contrary to their independence in the selected basis. Each ridge equation therefore gives zero or the sole later coefficient times an incidence sign.

## References

- Truth anchor: `D5/S3/TotalVariation/FairBiasCycleCoefficients.normalized_cycle_unit_coefficients`
- Dependency: [D5/S3/TotalVariation/FairBiasChainContraction](FairBiasChainContraction.md)
