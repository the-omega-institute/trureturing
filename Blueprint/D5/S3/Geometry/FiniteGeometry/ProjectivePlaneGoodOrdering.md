# Original coordinates, complete zero supports, and finite counting

## Abstract

Literal Good orders of all original points of arbitrary finite projective planes.

Let P and L be the actual point and line types of an arbitrary finite nondegenerate projective plane. The derived order q is at least two, the number of points and lines is n=q^2+q+1, and each line has q+1 original points. The plane need not be Desarguesian. No existence of a plane for each integer q is assumed. lineSupport is precisely the original incidence support, not a substituted coordinate system.

**Definition 1.1 (Original line supports).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.lineSupport`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.lineSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

lineSupport l is the finite set of every original point incident with l.

**Theorem 1.2 (An original permutation with no line interval).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.exists_line_avoiding_order`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.exists_line_avoiding_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a literal List permutation of all original points in which no original line is a contiguous block. The generic ForbiddenContiguousBlocks.block_card counts each bad line event exactly as (q+1)!*(n-q)!, by actual compression and expansion. Double counting gives total bad incidences n*(q+1)!*(n-q)!. For every q at least three, monotonicity of binomial coefficients up to the middle and the explicit third-coefficient estimate make this strictly smaller than n!. At q=2 the counts are equal; two different original lines meet at one point, and their two complementary pieces, that point, and all remaining points give one actual order with two bad incidences. The generic equality-with-overlap theorem forces an order with zero bad incidences. This is neither a Fano enumeration nor a probabilistic independence argument.

**Definition 1.3 (The complete minimal zero-support predicate).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.MinimalZero`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.MinimalZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A support is nonempty, proper in all original points, has label sum zero, and has no strictly smaller nonempty zero support. Its labels may lie in any additive commutative group and may repeat.

**Theorem 1.4 (From complete minimal rows to all proper zero supports).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.zero_support_iff_line_of_complete_minimals`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.zero_support_iff_line_of_complete_minimals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume literally that ALL inclusion-minimal nonempty proper zero supports, and only those, are original line supports. Then a nonempty proper original support has sum zero if and only if it is an original line. Choose a minimal zero subset of a given zero support. If it is smaller, delete it; the nonempty remainder still has sum zero. A minimal zero subset of the remainder would be a second original line disjoint from the first. Actual projective-line intersection forbids this. Line-zero equations alone are not the completeness hypothesis.

**Theorem 1.5 (Literal Good in an arbitrary original group).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.good_of_complete_minimals`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.good_of_complete_minimals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under that complete-minimal-row hypothesis the full original label total is nonzero, and there is an ordering of ALL original indices whose mapped word is PairedZeroSubsetSpectrum.Good. Here Good means every interval 0<=i<j<=n other than the full (0,n) interval has nonzero sum. The support of a zero interval in the line-avoiding permutation would be an original line, a contradiction. Nonzero full total follows by taking the complement of a zero line and using that every line meets it. This theorem does not require injective labels or a torsion-free group, and it transfers no exact torsion orders to arbitrary groups.

**Definition 1.6 (An additive incidence map).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.incidenceHom`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.incidenceHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original integer incidence potential F is made into an additive homomorphism from Z^L to Z^P using its actual finite integer sums.

**Definition 1.7 (The exact additive integer range).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.integerImage`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.integerImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

integerImage is the AddSubgroup range of incidenceHom. No saturation, cancellation, extra relation, or rational span is introduced.

**Definition 1.8 (The universal original-coordinate quotient).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.Universal`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.Universal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Universal is the actual additive quotient Z^P / im_Z F.

**Definition 1.9 (The original unit classes).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.label`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

label x is exactly the quotient class of the original unit at x.

**Theorem 1.10 (Exact original lift of Boolean zero sums).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.sum_label_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.sum_label_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For EVERY finite original support S, its sum of unit classes is zero if and only if its original integer indicator belongs to the exact integer incidence range. The proof sums actual units and applies the quotient homomorphism and its exact zero criterion.

**Theorem 1.11 (Complete Boolean zero closure in the quotient).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.universal_zero_support_iff_line`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.universal_zero_support_iff_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty proper original support S, its label sum is zero exactly when S is an original line. This uses the previously reviewed and published ProjectivePlaneIntegerLattice.boolean_mem_lattice_iff on the original indicator, without adding any relation.

**Theorem 1.12 (Distinct nonzero original labels and a full Good word).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.universal_good`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.universal_good` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal quotient has injective, nonzero original unit labels, a nonzero full label total, and a literal Good word containing every original point exactly once. The mapped word is also nodup. Nonzero units use the previously proved signed-integer ideal q(q+1) at k=1; injectivity uses the original-difference ideal q; the full total uses its ideal q+1. Only integer divisibility is cancelled, never torsion in the quotient. The line-avoiding order and complete Boolean closure give the actual Good consumer. No general Good conjecture, AM assertion, or unrestricted integral blocker is claimed.

The new live inferential steps are the uniform strict count with its genuine equality-overlap repair, the complete-minimal to complete-zero closure, and their literal original-coordinate Good consumers. The standard finite-projective-plane, List, factorial, finite-sum and quotient APIs and the first published lattice increment are reused. Library searches are bounded to inspected declarations and make no global absence or novelty claim. Utility none: all arguments are symbolic over arbitrary finite planes and groups, without fixed-instance certificates, enumeration, checker or numeric reduction.

Native proof guidance: supplied projective-plane-integral-good-proof.txt, Sections 6-7, SHA256 a0e9d9886934e967a7f6c7b189d708b5012ae79b5f2ba573b5e106f8e68ca18c. Guidance is not kernel evidence. Four-slot escape registration is unfinished and disclosed at https://github.com/the-omega-institute/trureturing/issues/22019; no declared_validated claim is made.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.MinimalZero`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.Universal`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.exists_line_avoiding_order`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.good_of_complete_minimals`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.incidenceHom`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.integerImage`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.label`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.lineSupport`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.sum_label_zero_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.universal_good`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.universal_zero_support_iff_line`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering.zero_support_iff_line_of_complete_minimals`
- Dependency: [D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks](../../Combinatorics/Permutation/ForbiddenContiguousBlocks.md)
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum](../../Combinatorics/Sequenceability/PairedZeroSubsetSpectrum.md)
- Dependency: [D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice](ProjectivePlaneIntegerLattice.md)
