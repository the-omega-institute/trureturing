# Exact sections of the original normalized base

## Abstract

The singleton center image is an exact transverse section of the original base.

Let C be a closed, generating pointed cone in a finite-dimensional real normed space V, and let u be a linear functional strictly positive on nonzero vectors of C. Write K for the entire normalized base and P for all its extreme points. Each whole exclusion D(p) uses the entire original proper effect interval. Binary compatibility compares all original pure endpoints at independent weights in the closed unit interval, including repeated endpoints and zero weights.

**Theorem 1.1 (The exact section of a singleton-label ball).**

Lean statement: `D5/S3/Quantum/Foundation/BinaryCenterSections.whole_ball_center_section`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterSections.whole_ball_center_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the original exclusions are whole positive-dimensional affine balls and satisfy binary compatibility. For each original p with a singleton label and every whole chart b of D(p), an affine map g agrees on each unit vector with the center of the corresponding original pure point. It is injective with linear rank b.dim. Every point of norm strictly below one maps to the relative interior of K. The image of the whole closed unit ball equals K intersect the range of g. For each unit vector, the range of the linear part of g is disjoint from the linear direction of the corresponding whole original exclusion.

Apply the whole-ball center graph to obtain the original boundary centers and the singleton rank branch. If an interior source point maps to the relative frontier of K, an original exposing effect vanishes there. Its composition with g is nonnegative on the source ball and therefore vanishes on the entire source chart. Each original boundary center forces its whole exclusion into the same exposed face, so whole-face maximality and center uniqueness identify all boundary values. This contradicts injectivity.

A point of K in the affine range beyond the ball would place an original boundary center on the open segment from the interior image center to that point. Every such point on the segment lies in the relative interior of K. The resulting exact section implies transversality. A nonzero shared direction would give two points of the section on either side of a boundary center, which is an extreme point of the image ball.

**Theorem 1.2 (The original three-dimensional sections and dimension bound).**

Lean statement: `D5/S3/Quantum/Foundation/BinaryCenterSections.original_center_sections`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterSections.original_center_sections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume V is nontrivial and each entire original exclusion has a three-dimensional ball chart. Under binary compatibility, the affine dimension of K is at least six and an original singleton-label exclusion exists. For every such label, there is an entire three-dimensional chart and an injective rank-three affine g agreeing with the original centers on its sphere. Its interior image lies in the relative interior of K and its closed-ball image equals K intersect the affine span of that image. The intrinsic frontier of the image equals its sphere image, contained in the intrinsic frontier of K. For every unit source vector, the image direction is disjoint from the direction of the corresponding whole original exclusion.

The chart closed ball affinely spans its carrier. Affine transport of the intrinsic frontier identifies the entire boundary of the image with the original boundary centers. The singleton-label existence theorem and the original normalized-base dimension identity give the global conclusions for this same K.

Source §138.3 of Quantum Origin XI. https://github.com/the-omega-institute/trureturing-source-theories/blob/2a39da5107abbfa3a72cc883486dbc15a15994a1/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md#L1318-L1345

## References

- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterSections.original_center_sections`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterSections.whole_ball_center_section`
- Dependency: [D5/S3/Quantum/Foundation/ActualExclusionBoundary](ActualExclusionBoundary.md)
- Dependency: [D5/S3/Quantum/Foundation/BinaryCenterGraph](BinaryCenterGraph.md)
- Dependency: [D5/S3/Quantum/Foundation/ExclusionIncidence](ExclusionIncidence.md)
- Dependency: [D5/S3/Quantum/Foundation/UniqueConfirmationDensity](UniqueConfirmationDensity.md)
