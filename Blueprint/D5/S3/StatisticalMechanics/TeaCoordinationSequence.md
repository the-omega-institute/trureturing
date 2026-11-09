# The coordination sequence of the tea slab graph

## Abstract

The tea slab graph has eight times its coordination number equal to 63n squared plus 16, 17, 12 or 17 according to the positive radius modulo four.

**Definition 1.1 (Triangular layers with alternating tetrahedral and prism slabs).**

$$\forall (u: \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z})), (\forall (v: \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z})), ((\operatorname{SimpleGraph.Adj}\left(\operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.teaGraph}, u, v\right)) \Leftrightarrow (((u.2.2 = v.2.2) \land (((v.1 = u.1 + 1) \land (v.2.1 = u.2.1)) \lor (((u.1 = v.1 + 1) \land (u.2.1 = v.2.1)) \lor (((v.1 = u.1) \land (v.2.1 = u.2.1 + 1)) \lor (((u.1 = v.1) \land (u.2.1 = v.2.1 + 1)) \lor (((v.1 = u.1 + 1) \land (u.2.1 = v.2.1 + 1)) \lor ((u.1 = v.1 + 1) \land (v.2.1 = u.2.1 + 1)))))))) \lor (((v.2.2 = u.2.2 + 1) \land (((v.1 = u.1) \land (v.2.1 = u.2.1)) \lor (((\operatorname{Int.emod}\left(u.2.2, 4\right) = 0) \land (((v.1 = u.1 + 1) \land (v.2.1 = u.2.1)) \lor ((v.1 = u.1) \land (v.2.1 = u.2.1 + 1)))) \lor ((\operatorname{Int.emod}\left(u.2.2, 4\right) = 2) \land (((v.1 = u.1 - 1) \land (v.2.1 = u.2.1)) \lor ((v.1 = u.1) \land (v.2.1 = u.2.1 - 1))))))) \lor ((u.2.2 = v.2.2 + 1) \land (((u.1 = v.1) \land (u.2.1 = v.2.1)) \lor (((\operatorname{Int.emod}\left(v.2.2, 4\right) = 0) \land (((u.1 = v.1 + 1) \land (u.2.1 = v.2.1)) \lor ((u.1 = v.1) \land (u.2.1 = v.2.1 + 1)))) \lor ((\operatorname{Int.emod}\left(v.2.2, 4\right) = 2) \land (((u.1 = v.1 - 1) \land (u.2.1 = v.2.1)) \lor ((u.1 = v.1) \land (u.2.1 = v.2.1 - 1)))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/TeaCoordinationSequence.teaGraph` (`✓ std3`).

*Citation.* N. J. A. Sloane, Colin Barker, Stefano Spezia (2018). *OEIS A299285, coordination sequence for the tea 3D uniform tiling*. URL: <https://oeis.org/A299285>.

*Commentary.*

Vertices are integer triples, with the third coordinate specifying the layer. Each layer is a triangular lattice: its six edge differences in the first two coordinates are (1,0), (−1,0), (0,1), (0,−1), (1,−1) and (−1,1). Between layers k and k+1 there is always an edge with unchanged horizontal coordinates. When k has remainder zero modulo four, there are also edges with horizontal shift (1,0) or (0,1); when its remainder is two, the additional shifts are (−1,0) or (0,−1). Odd layers have only the unchanged shift. The last two alternatives in the formula give both directions of the interlayer edges. This is the integer slab model of the tea net associated with OEIS A299285; the geometric identification with a tiling of three-dimensional space is outside the statement.

**Definition 1.2 (The coordination number at a radius).**

$$\forall (n: \mathbb{N}), ((\operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.shell}\left(n\right): \mathbb{N}) = \operatorname{Set.ncard}\left(\{v: \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z}) \mid \operatorname{SimpleGraph.dist}\left(\operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.teaGraph}, ((0, 0, 0): \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z})), v\right) = n\}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/TeaCoordinationSequence.shell` (`✓ std3`).

*Citation.* N. J. A. Sloane, Colin Barker, Stefano Spezia (2018). *OEIS A299285, coordination sequence for the tea 3D uniform tiling*. URL: <https://oeis.org/A299285>.

*Commentary.*

For every natural radius n, shell n is the natural cardinality of the vertices at graph distance exactly n from (0,0,0). Set.ncard is natural-valued, and the distance and layer counts below show that each sphere is finite. The center is this specified origin.

**Definition 1.3 (The four conjectural coordination formulas).**

$$(\operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), ((0 < n) \to (((\operatorname{Nat.mod}\left(n, 4\right) = 0) \to (8 \cdot \operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.shell}\left(n\right) = 63 \cdot n^{2} + 16)) \land (((\operatorname{Nat.mod}\left(n, 4\right) = 1) \to (8 \cdot \operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.shell}\left(n\right) = 63 \cdot n^{2} + 17)) \land (((\operatorname{Nat.mod}\left(n, 4\right) = 2) \to (8 \cdot \operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.shell}\left(n\right) = 63 \cdot n^{2} + 12)) \land ((\operatorname{Nat.mod}\left(n, 4\right) = 3) \to (8 \cdot \operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.shell}\left(n\right) = 63 \cdot n^{2} + 17)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/TeaCoordinationSequence.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker, Stefano Spezia (2018). *OEIS A299285, coordination sequence for the tea 3D uniform tiling*. URL: <https://oeis.org/A299285>.

*Commentary.*

The OEIS entry marks Barker's generating function and recurrence as conjectural and gives Spezia's closed form conditionally on them. Here that closed form is the proposition for the specified graph and origin: at every positive natural radius, eight times the coordination number is 63 times the squared radius plus the constant selected by its remainder modulo four. All four equalities are in the natural numbers. The generating function, recurrence and partial sums are not additional conjuncts.

**Definition 1.4 (Horizontal excess beyond a hexagonal region).**

$$\forall (i: \mathbb{Z}), (\forall (j: \mathbb{Z}), (\forall (p: \mathbb{Z}), (\forall (q: \mathbb{Z}), (\operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.residual}\left(i, j, p, q\right) = \operatorname{max}\left(0, \operatorname{max}\left(i - p, \operatorname{max}\left(j - p, \operatorname{max}\left(i + j - p, \operatorname{max}\left(-q - i, \operatorname{max}\left(-q - j, -q - i - j\right)\right)\right)\right)\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/TeaCoordinationSequence.residual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker, Stefano Spezia (2018). *OEIS A299285, coordination sequence for the tea 3D uniform tiling*. URL: <https://oeis.org/A299285>.

*Commentary.*

All four parameters are integers. The maximum measures the violations of the six bounds −q ≤ i,j,i+j ≤ p, together with zero. At p=q=0 it is the triangular lattice radius; at p=0 and q=1 its three negative coordinate bounds are shifted by one.

**Theorem 1.5 (The six bounds for the horizontal excess).**

$$\forall (i: \mathbb{Z}), (\forall (j: \mathbb{Z}), (\forall (p: \mathbb{Z}), (\forall (q: \mathbb{Z}), (\forall (d: \mathbb{Z}), ((\operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.residual}\left(i, j, p, q\right) \le d) \Leftrightarrow ((0 \le d) \land ((i \le p + d) \land ((j \le p + d) \land ((i + j \le p + d) \land ((-q - d \le i) \land ((-q - d \le j) \land (-q - d \le i + j))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/TeaCoordinationSequence.residual_le_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker, Stefano Spezia (2018). *OEIS A299285, coordination sequence for the tea 3D uniform tiling*. URL: <https://oeis.org/A299285>.

*Commentary.*

For arbitrary integers i, j, p, q and d, the horizontal excess is at most d exactly when d is nonnegative and each of i, j and i+j lies between −q−d and p+d. No sign assumptions on p or q are needed.

**Definition 1.6 (The finite hexagonal lattice region).**

$$\forall (p: \mathbb{Z}), (\forall (q: \mathbb{Z}), (\operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.hexagon}\left(p, q\right) = \operatorname{Finset.filter}\left(((z: \mathbb{Z} \times \mathbb{Z}) \mapsto ((-q \le z.1 + z.2) \land (z.1 + z.2 \le p))), \operatorname{Finset.product}\left(\operatorname{Finset.Icc}\left(-q, p\right), \operatorname{Finset.Icc}\left(-q, p\right)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/TeaCoordinationSequence.hexagon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker, Stefano Spezia (2018). *OEIS A299285, coordination sequence for the tea 3D uniform tiling*. URL: <https://oeis.org/A299285>.

*Commentary.*

For arbitrary integer endpoints p and q, filter the square interval [−q,p] squared by −q≤i+j≤p. This finite region is also used for the face-rooted simplex-inclusion graph of the triangular lattice.

**Theorem 1.7 (The six inequalities defining membership).**

$$\forall (p: \mathbb{Z}), (\forall (q: \mathbb{Z}), (\forall (i: \mathbb{Z}), (\forall (j: \mathbb{Z}), (((i, j) \in \operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.hexagon}\left(p, q\right)) \Leftrightarrow ((-q \le i) \land ((i \le p) \land ((-q \le j) \land ((j \le p) \land ((-q \le i + j) \land (i + j \le p))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/TeaCoordinationSequence.hexagon_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker, Stefano Spezia (2018). *OEIS A299285, coordination sequence for the tea 3D uniform tiling*. URL: <https://oeis.org/A299285>.

*Commentary.*

For all integers p, q, i and j, membership means that i, j and i+j each lie between −q and p. No sign conditions are required.

**Theorem 1.8 (The exact hexagonal lattice count).**

$$\forall (p: \mathbb{Z}), (\forall (q: \mathbb{Z}), ((0 \le p) \to ((0 \le q) \to (2 \cdot (\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(\operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.hexagon}\left(p, q\right)\right)\right): \mathbb{Z}) = p^{2} + 4 \cdot p \cdot q + q^{2} + 3 \cdot p + 3 \cdot q + 2))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/TeaCoordinationSequence.hexagon_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker, Stefano Spezia (2018). *OEIS A299285, coordination sequence for the tea 3D uniform tiling*. URL: <https://oeis.org/A299285>.

*Commentary.*

For nonnegative integer p and q, twice the integer cast of the region's cardinality is p²+4pq+q²+3p+3q+2. This is the shared counting statement for the tea regions and the vertex and face slices of the kisrhombille ball.

**Theorem 1.9 (The coordination formulas hold at every positive radius).**

$$\forall (n: \mathbb{N}), ((0 < n) \to (((\operatorname{Nat.mod}\left(n, 4\right) = 0) \to (8 \cdot \operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.shell}\left(n\right) = 63 \cdot n^{2} + 16)) \land (((\operatorname{Nat.mod}\left(n, 4\right) = 1) \to (8 \cdot \operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.shell}\left(n\right) = 63 \cdot n^{2} + 17)) \land (((\operatorname{Nat.mod}\left(n, 4\right) = 2) \to (8 \cdot \operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.shell}\left(n\right) = 63 \cdot n^{2} + 12)) \land ((\operatorname{Nat.mod}\left(n, 4\right) = 3) \to (8 \cdot \operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.shell}\left(n\right) = 63 \cdot n^{2} + 17))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/TeaCoordinationSequence.result` (`✓ std3`). ∎

*Resolves.* `Problems/barker-2018-oeis-a299285-tea-coordination-sequence` (proved) by `D5/S3/StatisticalMechanics/TeaCoordinationSequence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"barker-2018-oeis-a299285-tea-coordination-sequence","declaration_gid":"D5/S3/StatisticalMechanics/TeaCoordinationSequence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker, Stefano Spezia (2018). *OEIS A299285, coordination sequence for the tea 3D uniform tiling*. URL: <https://oeis.org/A299285>.

*Commentary.*

For a layer k, count separately the two orientations of tetrahedral slabs crossed from layer zero. For nonnegative k these counts are (k+3)/4 and (k+1)/4; for negative k they are (−k+2)/4 and (−k)/4. They are nonnegative integers. All divisions of integers here and in the distance formula are Lean's floor division Int.ediv. For nonnegative integer counts p and q, measure the horizontal excess by the maximum of zero and the six violations of the bounds −q ≤ i,j,i+j ≤ p. Being at most d is exactly the conjunction of d being nonnegative and the six bounds with endpoints −q−d and p+d.

Add the absolute layer coordinate to the natural conversion of this maximum. Along a planar edge the maximum changes by at most one. For an interlayer edge, split according to the sign of the layer and its remainder modulo four. The slab counts and the permitted horizontal shifts make the whole natural-valued expression change by at most one.

When the maximum is positive, a planar step decreases it by exactly one: split according to the signs of i and j and move toward the hexagonal region. When it is zero and the layer is nonzero, move one layer toward zero. Removing a slab of the first orientation either leaves the horizontal coordinates unchanged or subtracts one from one coordinate; removing the other orientation either leaves them unchanged or adds one to one coordinate. The six bounds ensure that one permitted choice lies in the smaller region. A prism step leaves the coordinates unchanged. These steps decrease the whole expression by exactly one. Value zero forces all three coordinates to be zero. Strong induction constructs a walk from the origin of exactly that length, proving the upper distance bound. Apply the edge estimate along a walk in the reverse direction, using value zero at the origin, to obtain the lower bound. Thus the exact distance is:

$$
\forall (i: \mathbb{Z}), (\forall (j: \mathbb{Z}), (\forall (k: \mathbb{Z}), (\operatorname{SimpleGraph.dist}\left(\operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.teaGraph}, ((0, 0, 0): \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z})), (i, j, k)\right) = \operatorname{Int.natAbs}\left(k\right) + \operatorname{Int.toNat}\left(\operatorname{max}\left(0, \operatorname{max}\left(i - \operatorname{ite}\left(0 \le k, \operatorname{Int.ediv}\left((k + 3: \mathbb{Z}), (4: \mathbb{Z})\right), \operatorname{Int.ediv}\left((-k + 2: \mathbb{Z}), (4: \mathbb{Z})\right)\right), \operatorname{max}\left(j - \operatorname{ite}\left(0 \le k, \operatorname{Int.ediv}\left((k + 3: \mathbb{Z}), (4: \mathbb{Z})\right), \operatorname{Int.ediv}\left((-k + 2: \mathbb{Z}), (4: \mathbb{Z})\right)\right), \operatorname{max}\left(i + j - \operatorname{ite}\left(0 \le k, \operatorname{Int.ediv}\left((k + 3: \mathbb{Z}), (4: \mathbb{Z})\right), \operatorname{Int.ediv}\left((-k + 2: \mathbb{Z}), (4: \mathbb{Z})\right)\right), \operatorname{max}\left(-\operatorname{ite}\left(0 \le k, \operatorname{Int.ediv}\left((k + 1: \mathbb{Z}), (4: \mathbb{Z})\right), \operatorname{Int.ediv}\left((-k: \mathbb{Z}), (4: \mathbb{Z})\right)\right) - i, \operatorname{max}\left(-\operatorname{ite}\left(0 \le k, \operatorname{Int.ediv}\left((k + 1: \mathbb{Z}), (4: \mathbb{Z})\right), \operatorname{Int.ediv}\left((-k: \mathbb{Z}), (4: \mathbb{Z})\right)\right) - j, -\operatorname{ite}\left(0 \le k, \operatorname{Int.ediv}\left((k + 1: \mathbb{Z}), (4: \mathbb{Z})\right), \operatorname{Int.ediv}\left((-k: \mathbb{Z}), (4: \mathbb{Z})\right)\right) - i - j\right)\right)\right)\right)\right)\right)\right))))
$$

Next fix nonnegative integer counts p and q. The zero-excess region consists of the integer pairs with all three of i, j and i+j between −q and p. Count its points by vertical slices. For each first coordinate i from −q through p, the second coordinate ranges from max(−q,−q−i) to min(p,p−i). Split the first coordinate into −q through −1 and zero through p; the slice lengths are p+q+1+i and p+q+1−i respectively. The half-open interval sum identity for complex casts gives, after casting back to integers, twice the sum of an integer interval as the sum of its endpoints times its cardinality. Summing the slice lengths therefore gives the following count. Nat.cast explicitly includes the natural cardinality in the integers:

$$
\forall (p: \mathbb{Z}), (\forall (q: \mathbb{Z}), ((0 \le p) \to ((0 \le q) \to (2 \cdot (\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(\operatorname{D5.S3.StatisticalMechanics.TeaCoordinationSequence.hexagon}\left(p, q\right)\right)\right): \mathbb{Z}) = p^{2} + 4 \cdot p \cdot q + q^{2} + 3 \cdot p + 3 \cdot q + 2))))
$$

At excess d greater than zero, the pairs form the difference of two nested hexagonal regions: the outer endpoints are −q−d and p+d, and the inner endpoints are −q−d+1 and p+d−1. Subtracting their cardinalities gives 3(p+q)+6d, as an integer count. At excess zero use the hexagonal count just established.

For radius n, use the exact distance to partition the sphere into the integer layers from −n through n. In layer k the excess is the natural difference n−Int.natAbs k, and the two slab counts are those specified above. The finite horizontal regions embed injectively as (i,j,k); different layers are disjoint. A bijection with their dependent union therefore expresses shell n as the sum of their finite cardinalities.

Assume n is positive and cast the layer counts to integers. Pair each nonnegative layer m with layer −m. The four slab counts in such a pair sum to m. For m less than n the positive-excess count consequently makes the paired contribution 12n−9m; at m=0 this counts the middle layer twice, whose contribution is 6n. At the two extreme layers the excess is zero. Twice their combined count is the sum, over those two layers, of the squares of the two slab counts plus four times their product, together with 3n+4. Pairing the full layer sum, subtracting the extra middle contribution and using twice the sum of zero through n−1 equal to n(n−1) shows that eight times shell n is 60n²+16 plus four times that sum of quadratic slab-count terms.

Finally split n into its four remainders modulo four and use the integer quotient n/4, again with floor division Int.ediv. At remainder zero all four extreme-layer slab counts equal the quotient. At remainder one only the first count in layer n is one larger. At remainder two the first count in each extreme layer is one larger. At remainder three both counts in layer n and the first count in layer −n are one larger. Substitution into the quadratic expression gives the constants 16, 17, 12 and 17 respectively after collecting 63n². Casting the equalities back to natural numbers proves the four implications. Replacing the layer sum by shell n proves their conjunction for every positive n.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/TeaCoordinationSequence.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/TeaCoordinationSequence.hexagon`
- Truth anchor: `D5/S3/StatisticalMechanics/TeaCoordinationSequence.hexagon_card`
- Truth anchor: `D5/S3/StatisticalMechanics/TeaCoordinationSequence.hexagon_mem`
- Truth anchor: `D5/S3/StatisticalMechanics/TeaCoordinationSequence.residual`
- Truth anchor: `D5/S3/StatisticalMechanics/TeaCoordinationSequence.residual_le_iff`
- Truth anchor: `D5/S3/StatisticalMechanics/TeaCoordinationSequence.result`
- Truth anchor: `D5/S3/StatisticalMechanics/TeaCoordinationSequence.shell`
- Truth anchor: `D5/S3/StatisticalMechanics/TeaCoordinationSequence.teaGraph`
- Dependency: [D5/S1/Recurrence/Bilateral/HannaThetaFourModFour](../../S1/Recurrence/Bilateral/HannaThetaFourModFour.md)
- Dependency: [D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation](../Combinatorics/PositionSets/VertexPositionRatioRefutation.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockVirasoroSpectrum](../VertexAlgebra/LatticeHalfFockVirasoroSpectrum.md)
