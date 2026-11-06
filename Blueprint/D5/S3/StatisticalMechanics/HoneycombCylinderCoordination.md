# Coordination sequences of diagonal honeycomb cylinders

## Abstract

The coordination sequence of every diagonal honeycomb cylinder satisfies the generating-function identity conjectured in OEIS A329512.

OEIS A329512, revision 40, calls row n the coordination sequence for a cylinder formed by rolling up a strip of width 2n hexagons, cut perpendicular to grid lines. The coordinate model identifies translation through (n,n). All positive natural n are quantified. False labels A vertices and true labels B vertices; each vertex is a nested pair (label,(i,j)). In the formulas, fst and snd are the literal product projections. The formulas display the edge relation and the diagonal translation explicitly.

**Definition 1.1 (The labeled integer lattice).**

$$Vertex = Bool \times (\mathbb{Z} \times (\mathbb{Z}))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane (2019). *OEIS A329512: coordination sequences of honeycomb cylinders of width 2n*. URL: <https://oeis.org/A329512>.

*Commentary.*

The coordinates i and j range independently over all integers.

**Definition 1.2 (The literal honeycomb graph).**

$$\forall u: Vertex, (\forall v: Vertex, ((\operatorname{SimpleGraph.Adj}\left(honeycombGraph, u, v\right)) \iff (((\operatorname{Prod.fst}\left(u\right) = false) \land ((\operatorname{Prod.fst}\left(v\right) = true) \land (((\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(u\right)\right) = \operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(v\right)\right)) \land (\operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(u\right)\right) = \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(v\right)\right))) \lor (((\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(u\right)\right) = \operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(v\right)\right) + 1) \land (\operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(u\right)\right) = \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(v\right)\right))) \lor ((\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(u\right)\right) = \operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(v\right)\right)) \land (\operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(u\right)\right) = \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(v\right)\right) + 1)))))) \lor ((\operatorname{Prod.fst}\left(v\right) = false) \land ((\operatorname{Prod.fst}\left(u\right) = true) \land (((\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(v\right)\right) = \operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(u\right)\right)) \land (\operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(v\right)\right) = \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(u\right)\right))) \lor (((\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(v\right)\right) = \operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(u\right)\right) + 1) \land (\operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(v\right)\right) = \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(u\right)\right))) \lor ((\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(v\right)\right) = \operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(u\right)\right)) \land (\operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(v\right)\right) = \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(u\right)\right) + 1)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.honeycombGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane (2019). *OEIS A329512: coordination sequences of honeycomb cylinders of width 2n*. URL: <https://oeis.org/A329512>.

*Commentary.*

The neighbours of A(i,j) are B(i,j), B(i−1,j) and B(i,j−1). The second disjunct supplies the reverse edges. The Boolean labels differ along every edge, so the graph has no loops.

**Definition 1.3 (Integral powers of the translation).**

$$\forall n: \mathbb{N}, (\forall u: Vertex, (\forall v: Vertex, ((\operatorname{Setoid.r}\left(\operatorname{translationSetoid}\left(n\right), u, v\right)) \iff (\exists k: \mathbb{Z}, ((\operatorname{Prod.fst}\left(u\right), (\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(u\right)\right) + (n: \mathbb{Z}) \cdot k, \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(u\right)\right) + (n: \mathbb{Z}) \cdot k)) = v)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.translationSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane (2019). *OEIS A329512: coordination sequences of honeycomb cylinders of width 2n*. URL: <https://oeis.org/A329512>.

*Commentary.*

The integer k may have either sign or be zero. The Boolean label is fixed. The cast of n to the integers is taken before multiplication by k.

**Definition 1.4 (The quotient vertex type).**

$$\forall n: \mathbb{N}, (\operatorname{Cylinder}\left(n\right) = \operatorname{Quotient}\left(\operatorname{translationSetoid}\left(n\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.Cylinder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane (2019). *OEIS A329512: coordination sequences of honeycomb cylinders of width 2n*. URL: <https://oeis.org/A329512>.

*Commentary.*

The quotient is by precisely the displayed translation equivalence relation.

**Definition 1.5 (The quotient simple graph).**

$$\forall n: \mathbb{N}, (\operatorname{cylinderGraph}\left(n\right) = \operatorname{SimpleGraph.map}\left(\operatorname{Quotient.mk}\left(\operatorname{translationSetoid}\left(n\right)\right), honeycombGraph\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.cylinderGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane (2019). *OEIS A329512: coordination sequences of honeycomb cylinders of width 2n*. URL: <https://oeis.org/A329512>.

*Commentary.*

SimpleGraph.map puts an edge between distinct quotient vertices when adjacent representatives exist. No honeycomb edge collapses, because translation preserves the Boolean label. The projection therefore maps walks to walks without changing their length.

**Definition 1.6 (The specified center).**

$$\forall n: \mathbb{N}, (\operatorname{origin}\left(n\right) = \operatorname{Quotient.mk}\left(\operatorname{translationSetoid}\left(n\right)\right)\left((false, (0, 0))\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.origin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane (2019). *OEIS A329512: coordination sequences of honeycomb cylinders of width 2n*. URL: <https://oeis.org/A329512>.

*Commentary.*

The center is the class of A(0,0).

**Definition 1.7 (The literal finite shell cardinality).**

$$\forall n: \mathbb{N}, (\forall m: \mathbb{N}, (\operatorname{c}\left(n, m\right) = \operatorname{Nat.card}\left(\operatorname{Subtype}\left(\lambda v: \operatorname{Cylinder}\left(n\right) \mapsto (\operatorname{SimpleGraph.dist}\left(\operatorname{cylinderGraph}\left(n\right), \operatorname{origin}\left(n\right), v\right) = m)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.c` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane (2019). *OEIS A329512: coordination sequences of honeycomb cylinders of width 2n*. URL: <https://oeis.org/A329512>.

*Commentary.*

SimpleGraph.dist is the minimum walk length. Every quotient vertex is reachable from the center. The proof identifies every shell with a finite sum of finite integer-coordinate fibers, proving finiteness for every positive n and every natural radius, including zero. Nat.card counts the subtype in the formula; no proposed shell formula is used in its definition.

**Theorem 1.8 (The all-width formal series identity).**

$$\forall n: \mathbb{N}, ((1 \leq n) \to ((1 - \operatorname{PowerSeries.X})^{2} \cdot \operatorname{PowerSeries.mk}\left(\lambda m: \mathbb{N} \mapsto ((\operatorname{c}\left(n, m\right): \mathbb{Z}))\right) = (1 - \operatorname{PowerSeries.X}) \cdot (1 + 2 \cdot \operatorname{PowerSeries.X} - \operatorname{PowerSeries.C}\left((n: \mathbb{Z}) - 2\right) \cdot \operatorname{PowerSeries.X}^{2 \cdot n} - \operatorname{PowerSeries.C}\left((n: \mathbb{Z}) - 1\right) \cdot \operatorname{PowerSeries.X}^{2 \cdot n + 1}) + 3 \cdot \operatorname{PowerSeries.X}^{2} \cdot (1 - \operatorname{PowerSeries.X}^{2 \cdot n - 2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.result` (`✓ std3`). ∎

*Resolves.* `Problems/sloane329512` (proved) by `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sloane329512","declaration_gid":"D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane (2019). *OEIS A329512: coordination sequences of honeycomb cylinders of width 2n*. URL: <https://oeis.org/A329512>.

*Commentary.*

Write s=i+j. On A vertices the plane distance is twice the maximum of 0, i, j, s, −i, −j and −s. On B vertices it is one plus twice the maximum of 0, i, j, s, −i−1, −j−1 and −s−1. Each edge changes this nonnegative potential by at most one. An explicit adjacent vertex decreases every positive potential by one; strong induction constructs a walk attaining the bound. The generic potential bound supplies the opposite inequality, so these are genuine graph distances.

Every quotient walk lifts from any chosen initial representative, with its length preserved. Thus quotient distance is the minimum of the plane distances of representatives. Every A class has a unique representative with −n<s≤n; every B class has a unique representative with −n≤s<n. Euclidean division constructs these representatives. The six inequalities in the potential prove that each is minimizing. Integer division uses a nonnegative remainder modulo the positive integer 2n.

At plane A-radius 2k with k>0, each slice −k<s<k contributes two points, and each boundary slice s=k or s=−k contributes k+1. Intersecting with the A strip gives 6k when 0<k<n, 5n−1 when k=n, and 4n when k>n. At B-radius 2k+1, the interior slices −k≤s<k contribute two each, and the boundary slices s=k and s=−k−1 contribute k+1 and k+2. Intersecting with the B strip gives 6k+3 for k<n and 4n otherwise. The radius-zero count is one. Hence the count at positive radius m is 3m before 2n, 5n−1 at 2n, and 4n after it.

PowerSeries.mk assigns the integer-cast shell count to each coefficient. Comparing second differences proves the displayed identity. C is the PowerSeries constant-series map. In C((n:ℤ)−2) and C((n:ℤ)−1), subtraction is in the integers; the first coefficient is −1 at n=1. Subtraction in 2n−2 is natural truncated subtraction and n≥1 makes it nonnegative. The source uses two factors of 1/(1−X). Since 1−X has constant coefficient one, it is a unit in the integer formal series ring. Multiplying by its square gives exactly the displayed equivalent cleared identity. No convergence hypothesis or statement about a physical nanotube is involved.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.Cylinder`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.Vertex`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.c`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.cylinderGraph`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.honeycombGraph`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.origin`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.result`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.translationSetoid`
- Dependency: [D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation](../Combinatorics/PositionSets/VertexPositionRatioRefutation.md)
