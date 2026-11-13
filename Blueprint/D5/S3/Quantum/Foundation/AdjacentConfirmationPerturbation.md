# A specified perturbation of an adjacent complete confirmer

## Abstract

An adjacent complete confirmer admits a positive perturbation with smaller global range; normalization in the original unit strictly increases its contrast on the whole exclusion ball.

The carrier is an arbitrary finite dimensional real normed space. The original cone C is closed, pointed and generating; the original linear unit u is strictly positive on every nonzero cone vector. K is the entire base with u=1, P is its entire extreme-point set, and proper effects are all linear functionals between zero and u on C. Every entire exclusion D(p) is an injective affine image of a positive-dimensional closed Euclidean ball, and different original pure labels have different exclusions. The original three-dimensional ball setting is included.

**Theorem 1.1 (Global contraction and strict whole-ball contrast gain).**

Lean statement: `D5/S3/Quantum/Foundation/AdjacentConfirmationPerturbation.adjacent_confirmation_perturbation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/AdjacentConfirmationPerturbation.adjacent_confirmation_perturbation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take original pure labels p,q with q in D(p). The proper effect a confirms q and vanishes on all of D(q); the proper effect e confirms p and vanishes on all of D(p). Suppose M<1 bounds the contrast of every original effect on every ordered pair in D(q). Then there is one t>0 for which g=a+t e has actual global minimum lo and maximum hi on K, with 0<hi-lo<1. The original-unit normalization b=(g-lo*u)/(hi-lo) is proper on the entire original cone. Its oscillation on the whole D(p) is strictly greater than that of a, and the latter is strictly positive. The extrema are attained by actual original states.

The width premise concerns only D(q). In particular it follows when M is the global supremum of the widths of all original exclusions and M<1. The condition q in P intersect D(p) is exactly an original pure adjacent point; the whole-ball facial description identifies these points with the sphere of D(p). No uniqueness of the complete confirmer, compactness of P, common center, pair-face completion, or unit-preserving retraction is assumed.

The whole one-value face of a is the singleton q. Original exclusion symmetry puts p in D(q). Thus if a(x)=1 and a(y)=0 for original states x,y, then x=q, e(x)=0, and the width bound applied to e on p,y gives e(y)>=1-M>0. The compact adverse-pair set consists of pairs (x,y) in K times K with e(y)<=e(x). On that entire set the a-contrast is strictly below one, so its actual maximum has a positive gap below one. Half this gap gives a single positive t controlling every adverse pair. On the complementary pairs, the perturbation decreases contrast strictly. Hence every ordered contrast of g is below one.

Since e vanishes on all of D(p), the perturbation preserves every a-contrast there. The nonpoint ball and the singleton one-value face provide a second point with a-value below one, proving strict positive oscillation. Compactness supplies the actual global extrema of g, whose difference is positive and below one. Subtracting lo times the same original unit and dividing by this difference yields an effect in the full original interval. Its oscillation on D(p) is exactly the old oscillation divided by hi-lo, proving strict gain.

This proof constructs the specified perturbation directly by compactness and contact geometry. It establishes no general formula for one-sided derivatives of maxima or minima, no statement about moving exclusion faces, and no automatic global width-one conclusion. It is a deduction in the stated original convex model; it asserts no physical implementation or literature priority.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/AdjacentConfirmationPerturbation.adjacent_confirmation_perturbation`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionWidthCompactness](ExclusionWidthCompactness.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalWidthContact](OriginalWidthContact.md)
