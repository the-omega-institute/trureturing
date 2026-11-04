# The coordination sequence of the alternating prism graph

## Abstract

The alternating prism graph has coordination numbers (13n squared + 4)/2 at positive even radii and (13n squared + 3)/2 at odd radii.

**Definition 1.1 (Square layers with alternating prism slabs).**

$$\forall (u: \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z})), (\forall (v: \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z})), ((\operatorname{SimpleGraph.Adj}\left(\operatorname{D5.S3.StatisticalMechanics.TsiCoordinationSequence.tsiGraph}, u, v\right)) \Leftrightarrow (((u.2.2 = v.2.2) \land ((u.2.1 = v.2.1) \land ((u.1 = v.1 + 1) \lor (v.1 = u.1 + 1)))) \lor (((u.2.2 = v.2.2) \land ((u.1 = v.1) \land ((u.2.1 = v.2.1 + 1) \lor (v.2.1 = u.2.1 + 1)))) \lor (((v.2.2 = u.2.2 + 1) \land (((v.1 = u.1) \land (v.2.1 = u.2.1)) \lor (((\operatorname{Even}\left(u.2.2\right)) \land ((v.1 = u.1 + 1) \land (v.2.1 = u.2.1))) \lor ((\operatorname{Odd}\left(u.2.2\right)) \land ((v.1 = u.1) \land (v.2.1 = u.2.1 + 1)))))) \lor ((u.2.2 = v.2.2 + 1) \land (((u.1 = v.1) \land (u.2.1 = v.2.1)) \lor (((\operatorname{Even}\left(v.2.2\right)) \land ((u.1 = v.1 + 1) \land (u.2.1 = v.2.1))) \lor ((\operatorname{Odd}\left(v.2.2\right)) \land ((u.1 = v.1) \land (u.2.1 = v.2.1 + 1)))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/TsiCoordinationSequence.tsiGraph` (`✓ std3`).

*Citation.* N. J. A. Sloane, Colin Barker (2018). *OEIS A299289, coordination sequence for the tsi 3D uniform tiling*. URL: <https://oeis.org/A299289>.

*Commentary.*

The vertices are integer triples, with the third coordinate specifying the layer. Within each layer, adjacent vertices differ by one in exactly one horizontal coordinate. From layer k to layer k+1, each vertex is joined to the vertex with the same horizontal coordinates and to one shifted by one in the first coordinate when k is even, or in the second coordinate when k is odd. The last two alternatives include both directions of these interlayer edges. This is the combinatorial alternating prism model of the tsi net; its geometric realization as a tiling is not part of the statement.

**Definition 1.2 (The coordination number at a radius).**

$$\forall (n: \mathbb{N}), ((\operatorname{D5.S3.StatisticalMechanics.TsiCoordinationSequence.shell}\left(n\right): \mathbb{N}) = \operatorname{Set.ncard}\left(\{v: \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z}) \mid \operatorname{SimpleGraph.dist}\left(\operatorname{D5.S3.StatisticalMechanics.TsiCoordinationSequence.tsiGraph}, ((0, 0, 0): \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z})), v\right) = n\}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/TsiCoordinationSequence.shell` (`✓ std3`).

*Citation.* N. J. A. Sloane, Colin Barker (2018). *OEIS A299289, coordination sequence for the tsi 3D uniform tiling*. URL: <https://oeis.org/A299289>.

*Commentary.*

For every natural radius n, shell n counts the vertices at graph distance exactly n from the origin. Set.ncard is natural-valued; the distance formula below shows that each such sphere is finite. The center is the specified vertex (0,0,0).

**Definition 1.3 (The two conjectural closed forms).**

$$(\operatorname{D5.S3.StatisticalMechanics.TsiCoordinationSequence.claim}) \Leftrightarrow ((\forall (n: \mathbb{N}), ((0 < n) \to ((\operatorname{Even}\left(n\right)) \to (2 \cdot \operatorname{D5.S3.StatisticalMechanics.TsiCoordinationSequence.shell}\left(n\right) = 13 \cdot n^{2} + 4)))) \land (\forall (n: \mathbb{N}), ((\operatorname{Odd}\left(n\right)) \to (2 \cdot \operatorname{D5.S3.StatisticalMechanics.TsiCoordinationSequence.shell}\left(n\right) = 13 \cdot n^{2} + 3))))$$

*Formalization.* `D5/S3/StatisticalMechanics/TsiCoordinationSequence.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A299289, coordination sequence for the tsi 3D uniform tiling*. URL: <https://oeis.org/A299289>.

*Commentary.*

The source labels the two formulas as conjectures. For the graph and center specified here, the proposition asserts the even formula at every positive even natural radius and the odd formula at every odd natural radius. Multiplication by two expresses both formulas as equalities of natural numbers. The generating function, recurrence and partial sums are not additional conjuncts.

**Theorem 1.4 (The coordination formulas hold at every positive radius).**

$$(\forall (n: \mathbb{N}), ((0 < n) \to ((\operatorname{Even}\left(n\right)) \to (2 \cdot \operatorname{D5.S3.StatisticalMechanics.TsiCoordinationSequence.shell}\left(n\right) = 13 \cdot n^{2} + 4)))) \land (\forall (n: \mathbb{N}), ((\operatorname{Odd}\left(n\right)) \to (2 \cdot \operatorname{D5.S3.StatisticalMechanics.TsiCoordinationSequence.shell}\left(n\right) = 13 \cdot n^{2} + 3)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/TsiCoordinationSequence.result` (`✓ std3`). ∎

*Resolves.* `Problems/barker-2018-oeis-a299289-tsi-coordination-sequence` (proved) by `D5/S3/StatisticalMechanics/TsiCoordinationSequence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"barker-2018-oeis-a299289-tsi-coordination-sequence","declaration_gid":"D5/S3/StatisticalMechanics/TsiCoordinationSequence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A299289, coordination sequence for the tsi 3D uniform tiling*. URL: <https://oeis.org/A299289>.

*Commentary.*

First measure the distance of an integer i from the integer interval with endpoints 0 and c as the natural number Int.toNat(min(0, c) − i) + Int.toNat(i − max(0, c)); Int.toNat sends a negative integer to zero.

For an integer triple (i,j,k), add the layer displacement Int.natAbs k, the distance of i from the interval with endpoints 0 and (k+1)/2, and the distance of j from the interval with endpoints 0 and k/2. These divisions are integer divisions, which round down for the divisor 2.

A horizontal edge changes this expression by at most one. To check an interlayer edge, split the absolute layer coordinate into the sum of the absolute values of (k+1)/2 and k/2. For even k only the first interval endpoint increases, and for odd k only the second increases. In either case, a shift by zero or one in that coordinate changes the corresponding absolute-value-plus-interval-distance term by at most one. Thus the expression changes by at most one along every edge.

Every vertex with a positive value has an adjacent vertex whose value is one smaller. If a horizontal coordinate is outside its interval, move it one unit toward that interval. Otherwise both coordinates are inside their intervals. Move the layer one step toward zero, adjusting the first or second coordinate at an endpoint as required by the parity and sign of k. The new coordinates remain in the smaller rectangle. Value zero forces all three coordinates to be zero. Strong induction therefore constructs a walk from the origin with length equal to the expression. This gives the upper bound on distance. Applying the edge estimate to the reverse reachable pair, with value zero at the origin, gives the lower bound. Hence, with integer division rounding down in the interval endpoints:

$$
\forall (i: \mathbb{Z}), (\forall (j: \mathbb{Z}), (\forall (k: \mathbb{Z}), (\operatorname{SimpleGraph.dist}\left(\operatorname{D5.S3.StatisticalMechanics.TsiCoordinationSequence.tsiGraph}, ((0, 0, 0): \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z})), (i, j, k)\right) = \operatorname{Int.natAbs}\left(k\right) + \operatorname{Int.toNat}\left(\operatorname{min}\left(0, \operatorname{HDiv.hDiv}\left((k + 1: \mathbb{Z}), (2: \mathbb{Z})\right)\right) - i\right) + \operatorname{Int.toNat}\left(i - \operatorname{max}\left(0, \operatorname{HDiv.hDiv}\left((k + 1: \mathbb{Z}), (2: \mathbb{Z})\right)\right)\right) + \operatorname{Int.toNat}\left(\operatorname{min}\left(0, \operatorname{HDiv.hDiv}\left((k: \mathbb{Z}), (2: \mathbb{Z})\right)\right) - j\right) + \operatorname{Int.toNat}\left(j - \operatorname{max}\left(0, \operatorname{HDiv.hDiv}\left((k: \mathbb{Z}), (2: \mathbb{Z})\right)\right)\right))))
$$

Next count the one-dimensional shells. At interval distance zero there are Int.natAbs c + 1 integers; at each positive interval distance there are exactly two, one beyond each endpoint. For a rectangle with interval endpoints (0,c) and (0,e), split a prescribed total distance d into t and d−t for t from zero through d. The resulting Cartesian products are disjoint because their first interval distances differ. Multiplying the interval counts gives (Int.natAbs c + 1)(Int.natAbs e + 1) at d=0. For d>0 the two end terms and the d−1 interior terms sum to 2(Int.natAbs c + Int.natAbs e) + 4d.

The sphere of radius n is the disjoint union of these rectangle shells over the integer layers from −n to n. In layer k the endpoints are (k+1)/2 and k/2, and the residual distance is n−Int.natAbs k. Embedding each horizontal pair as (i,j,k) is injective, and distinct layers are disjoint, so their finite cardinalities add to shell n.

For positive n, each of the two extreme layers has (n/2+1)((n+1)/2+1) vertices. In an interior layer the sum of the two absolute interval endpoints is Int.natAbs k, so the rectangle count simplifies to 4n−2 Int.natAbs k. Cast the layer counts to integers and use symmetry in k to sum over the nonnegative layers. The sum of the integers from zero through n−1 is evaluated by twice that sum being n(n−1). Converting the resulting equality back to natural numbers gives the following identity, in which the divisions on natural numbers are floor divisions, exactly Lean's Nat.div:

$$
\forall (n: \mathbb{N}), ((0 < n) \to (\operatorname{D5.S3.StatisticalMechanics.TsiCoordinationSequence.shell}\left(n\right) + 2 \cdot n = 6 \cdot n^{2} + 2 \cdot \left(\operatorname{HDiv.hDiv}\left((n: \mathbb{N}), (2: \mathbb{N})\right) + 1\right) \cdot \left(\operatorname{HDiv.hDiv}\left((n + 1: \mathbb{N}), (2: \mathbb{N})\right) + 1\right)))
$$

Finally, if n is positive and even, write n=t+t. Both n/2 and (n+1)/2 equal t; substitution into the sum identity yields 2 shell n = 13 n² + 4. If n is odd, write n=t+t+1. Then n is positive, n/2=t and (n+1)/2=t+1; the same identity yields 2 shell n = 13 n² + 3. These two arguments prove the two conjuncts.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/TsiCoordinationSequence.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/TsiCoordinationSequence.result`
- Truth anchor: `D5/S3/StatisticalMechanics/TsiCoordinationSequence.shell`
- Truth anchor: `D5/S3/StatisticalMechanics/TsiCoordinationSequence.tsiGraph`
- Dependency: [D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation](../Combinatorics/PositionSets/VertexPositionRatioRefutation.md)
