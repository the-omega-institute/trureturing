# Alternating Components and Maximal Steiner Switches

## Abstract

Large alternating components identify all successful starts in a point-deleted Steiner system.

**Definition 1.1 (The graph of the two pivot matchings).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.pivotGraph`

*Formalization.* `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.pivotGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write e(a) for the inclusion of the retained label a, skipping the deleted point and then adjoining an extra point to the carrier. Join each vertex to its partners under the translations through the deleted point and through e(v) for the fixed retained pivot v.

**Definition 1.2 (A successful starting label).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.SuccessfulStart`

*Formalization.* `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.SuccessfulStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a retained packing P and a partner map m on its labels, a start a is successful at pivot v if v differs from a and from m(a), and there exist labels b and d such that both {a,v,b} and {m(a),v,d} lie in P and d differs from m(b).

**Theorem 1.3 (All successful starting labels).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_successful_starts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_successful_starts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Delete any point q from a finite complete Steiner triple system on r+1 points and pull back the blocks avoiding q to the r retained labels. This is a partial Steiner system. One map m on the retained labels works for all pivots, with the pair a,b uncovered exactly when m(a)=b. Embed each retained label by first skipping q in the original point set and then including that point into the carrier with an adjoined point. For every retained pivot v, the component of the adjoined point is exactly that point, q, the embedded v, and the embedded m(v). The image of the successful starts under this embedding is exactly the set of vertices in components with at least six vertices in the union of the translations through q and the embedded v. If four divides r, the set of successful starts has at least six elements for every v.

The square containing the adjoined point also contains the deleted point, the retained pivot, and its leave partner. All vertices outside the square are eligible retained starts. Pair completion gives the two switch blocks. Their switch is successful exactly where the translations disagree in the two orders. Such a disagreement yields six distinct vertices reached by alternating steps. At a commuting vertex the four corners close under both matching steps. The enlarged carrier has r+2 points, so divisibility of r by four forces a large component.

**Theorem 1.4 (The first deficit without a switch hypothesis).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_first_deficit_of_four_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_first_deficit_of_four_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive row dimension d and nonzero residue modulus 3r. Suppose every pair (x,a),(y,b) from distinct rows occurs in a listed triple with specified third point (−(x+y),−(a+b)). Every listed triple has three distinct rows and product sum zero. A given pair of distinct points occurs in at most one indexed triple. If a complete Steiner system exists on r+1 points and four divides r, write N for 3^d r^2 plus 3^(d+1) times floor(r(r−2)/6). Internal extensions add distinct-point triples within rows, preserve pair uniqueness and keep the dimension of the normalized potential space equal to d+1. They are saturated when inclusion maximal among such extensions. There are saturated extensions with N and N−1 added triples, and every internal extension adds at most N triples.

Choose a successful start at any retained pivot and apply the one-class switch construction. The matching packing supplies the upper bound in every class.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.SuccessfulStart`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.pivotGraph`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_first_deficit_of_four_dvd`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_successful_starts`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations](SteinerMatchingTranslations.md)
