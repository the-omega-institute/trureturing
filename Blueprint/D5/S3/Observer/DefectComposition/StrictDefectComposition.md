# Strict Defect Composition

## Abstract

Strict difference defects add exactly under map composition.

**Theorem 1.1 (Strict difference defects form an additive chain).**

$$\delta_{M}(r\circ q;x,y) = \delta_{M}(q;x,y) + \delta_{M}(r;q\,x,q\,y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DefectComposition/StrictDefectComposition.strict_defect_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For source, intermediate, and target dissimilarity measures, define each defect as the strict source value minus the target value after applying its map.

For X to Y to Z, substituting the definitions makes the middle measure cancel. The result is exactly sub_add_sub_cancel, with no metric or regularity assumptions.

## References

- Truth anchor: `D5/S3/Observer/DefectComposition/StrictDefectComposition.strict_defect_composition`
