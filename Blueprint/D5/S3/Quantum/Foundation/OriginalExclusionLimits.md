# Original ball-parameter limit rank

## Abstract

Actual original parameter limits retain the whole mixed ball and have full rank or pure singleton image.

**Theorem 1.1 (Full rank or a pure singleton).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_parameter_limit_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_parameter_limit_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a nonzero finite dimensional real normed space, C the entire original closed generating pointed cone, and u the original strictly positive unit. Assume EB and pure PR. Fix original pure labels pn tending to the original pure p in the subspace topology. For every n let b(n) be an injective affine three-chart with its entire closed unit ball exactly D(pn). Suppose the actual centers b(n)(0) and actual linear parts converge together to c and A. The theorem proves c+A(z) belongs to the entire original D(p) for every mixed coordinate norm(z)<=1. It also proves either A is injective in all three directions, or A=0 and c is an original pure point in D(p).

Pointwise limits follow from the same joint center/operator convergence. The original closed incidence retains every mixed point. PR pure compactness retains every sphere point as an extreme point of the original K. The exact existing sphere_extreme_injective_or_zero owner is lawfully exposed and directly consumed: a flattened nonzero image would put the ball interior into the original extreme locus. No unit-width condition, weakPair, Inj, P0 restriction or global uniform-fiber hypothesis is used. The theorem does not identify the nonzero limit image with the entire D(p), prove every Hausdorff subsequence has one of the two exact whole-set limits, or conclude the IX115.6 continuity and local-budget equivalence. Those are additional topology obligations.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalExclusionLimits.original_parameter_limit_rank`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionUniformNoncollapse](ExclusionUniformNoncollapse.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalPureCompactness](OriginalPureCompactness.md)
