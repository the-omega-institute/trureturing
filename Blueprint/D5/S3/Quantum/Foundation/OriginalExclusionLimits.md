# Whole-P discontinuity witnesses and Baire regularity

## Abstract

Whole-P discontinuity witnesses and Baire regularity

V is an arbitrary finite dimensional real normed space, C its entire original pointed cone, and u the original linear unit. Assume C is closed and generating and u is strictly positive on nonzero C. K is the entire normalized base, P its entire extreme locus, and the effects and confirmers are the full original families, including u. EB3 parametrizes every whole exclusion, and PR exchanges only pure endpoints. All label neighborhoods use all P. No mixed PR, weakPair, RegularAnchor, global UF, prescribed saturation or matrix specialization is assumed.

**Theorem 1.1 (Every discontinuity supplies an actual whole-ball collapse).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_discontinuity_collapse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_discontinuity_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full original EB3 and pure PR hypotheses, at each Hausdorff discontinuity p there is a sequence pn of original pure labels tending to p and an actual pure q in D(p) such that the entire D(pn) tends to {q}. The proof directly consumes the frozen ReciprocalExclusionLimits.exclusion_limit_dichotomy, including its actual parameter extraction and exact whole-ball equality. If no such singleton subsequence exists, compactness of the entire family inside K makes every subsequence admit a further subsequence tending to the old whole D(p), proving continuity. This is not a conditional row premise. The stronger frozen ReciprocalPureCompactness.reciprocal_pure_compact supplies pure compactness without EB or nontriviality; no duplicate pure-compactness declaration is retained.

**Theorem 1.2 (Actual whole diameters on all P).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_diameter_upperSemicontinuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_diameter_upperSemicontinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function p -> diam(D(p)) is upper semicontinuous on all original pure labels. Each diameter upper layer is sequentially closed. Compactness in the hyperspace supplies an actual whole-set limit; the exact frozen dichotomy places that limit inside D(p). The diameter is Lipschitz with constant two on the nonempty compact hyperspace, so the threshold survives the limit.

**Theorem 1.3 (Open dense regular region and closed nowhere dense residual).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_baire_regular_region`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_baire_regular_region` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define S(j) by 1/(j+1)<=diam(D(p)), with j ranging over all natural numbers, and R as the union of their interiors in all P. Every S(j) is closed, and positive dimension makes every full diameter positive, so these layers cover P. Frozen pure compactness makes P a compact Baire space. Hence R is open and dense, and Sigma=P\R is closed and nowhere dense. This does not remove either residual collapse branch.

**Theorem 1.4 (Exact whole-ball continuity set).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_regular_iff_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_regular_iff_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure p, p belongs to R if and only if the actual whole-exclusion map is Hausdorff continuous at p. On an interior diameter layer an actual singleton collapse would contradict the positive lower bound and continuity of diameter. Conversely continuity at a nondegenerate old ball gives a positive diameter bound in an open neighborhood in all P. Equality with the continuity sets of the scalar coefficient a and actual optimal budget beta, and their whole-P semicontinuity, are additional obligations.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_baire_regular_region`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_diameter_upperSemicontinuous`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_discontinuity_collapse`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_regular_iff_continuous`
- Dependency: [D5/S3/Quantum/Foundation/ReciprocalExclusionLimits](ReciprocalExclusionLimits.md)
