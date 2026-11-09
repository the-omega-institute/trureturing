# Coordination sequences of odd-width honeycomb cylinders

## Abstract

The coordination sequence of every odd-width honeycomb cylinder satisfies the generating-function identity in OEIS A329515.

OEIS A329515, revision 32, gives the odd-width family with the half-hexagon seam offset. The coordinate model identifies (i,j) with (i+n+1,j+n), so the translation changes i+j by 2n+1. The shared Vertex and honeycombGraph are those of HoneycombCylinderCoordination. False labels A vertices and true labels B vertices; A(i,j) is adjacent to B(i,j), B(i−1,j) and B(i,j−1).

**Definition 1.1 (Integral powers of the offset translation).**

$$\forall n: \mathbb{N}, (\forall u: Vertex, (\forall v: Vertex, ((\operatorname{Setoid.r}\left(\operatorname{translationSetoid}\left(n\right), u, v\right)) \iff (\exists k: \mathbb{Z}, ((\operatorname{Prod.fst}\left(u\right), (\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(u\right)\right) + \left((n: \mathbb{Z}) + 1\right) \cdot k, \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(u\right)\right) + (n: \mathbb{Z}) \cdot k)) = v)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.translationSetoid` (`✓ std3`).

*Citation.* N. J. A. Sloane (2019). *OEIS A329515: coordination sequences of honeycomb cylinders of odd width 2n+1*. URL: <https://oeis.org/A329515>.

*Commentary.*

The integer k may have either sign or be zero. The Boolean label is fixed. The first coordinate receives n+1 and the second n.

**Definition 1.2 (The quotient vertex type).**

$$\forall n: \mathbb{N}, (\operatorname{Cylinder}\left(n\right) = \operatorname{Quotient}\left(\operatorname{translationSetoid}\left(n\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.Cylinder` (`✓ std3`).

*Citation.* N. J. A. Sloane (2019). *OEIS A329515: coordination sequences of honeycomb cylinders of odd width 2n+1*. URL: <https://oeis.org/A329515>.

*Commentary.*

The quotient is by precisely the displayed translation equivalence relation.

**Definition 1.3 (The quotient simple graph).**

$$\forall n: \mathbb{N}, (\operatorname{cylinderGraph}\left(n\right) = \operatorname{SimpleGraph.map}\left(\operatorname{Quotient.mk}\left(\operatorname{translationSetoid}\left(n\right)\right), honeycombGraph\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.cylinderGraph` (`✓ std3`).

*Citation.* N. J. A. Sloane (2019). *OEIS A329515: coordination sequences of honeycomb cylinders of odd width 2n+1*. URL: <https://oeis.org/A329515>.

*Commentary.*

SimpleGraph.map puts an edge between distinct quotient vertices when adjacent representatives exist.

**Definition 1.4 (The specified center).**

$$\forall n: \mathbb{N}, (\operatorname{origin}\left(n\right) = \operatorname{Quotient.mk}\left(\operatorname{translationSetoid}\left(n\right)\right)\left((false, (0, 0))\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.origin` (`✓ std3`).

*Citation.* N. J. A. Sloane (2019). *OEIS A329515: coordination sequences of honeycomb cylinders of odd width 2n+1*. URL: <https://oeis.org/A329515>.

*Commentary.*

The center is the class of A(0,0).

**Definition 1.5 (The literal finite shell cardinality).**

$$\forall n: \mathbb{N}, (\forall m: \mathbb{N}, (\operatorname{c}\left(n, m\right) = \operatorname{Nat.card}\left(\operatorname{Subtype}\left(\lambda v: \operatorname{Cylinder}\left(n\right) \mapsto (\operatorname{SimpleGraph.dist}\left(\operatorname{cylinderGraph}\left(n\right), \operatorname{origin}\left(n\right), v\right) = m)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.c` (`✓ std3`).

*Citation.* N. J. A. Sloane (2019). *OEIS A329515: coordination sequences of honeycomb cylinders of odd width 2n+1*. URL: <https://oeis.org/A329515>.

*Commentary.*

SimpleGraph.dist is the minimum walk length. Every quotient shell is finite, and c counts the subtype at the displayed distance.

**Theorem 1.6 (The all-width odd-cylinder formal series identity).**

$$\forall n: \mathbb{N}, ((1 - \operatorname{PowerSeries.X})^{2} \cdot \operatorname{PowerSeries.mk}\left(\lambda m: \mathbb{N} \mapsto ((\operatorname{c}\left(n, m\right): \mathbb{Z}))\right) = (1 - \operatorname{PowerSeries.X}) \cdot (1 + 2 \cdot \operatorname{PowerSeries.X} - \operatorname{PowerSeries.C}\left((n: \mathbb{Z}) - 2\right) \cdot \operatorname{PowerSeries.X}^{2 \cdot n + 1} - \operatorname{PowerSeries.C}\left((n: \mathbb{Z})\right) \cdot \operatorname{PowerSeries.X}^{2 \cdot n + 2}) + 3 \cdot \operatorname{PowerSeries.X}^{2} - 3 \cdot \operatorname{PowerSeries.X}^{2 \cdot n + 1})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.result` (`✓ std3`). ∎

*Resolves.* `Problems/sloane329515` (proved) by `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sloane329515","declaration_gid":"D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane (2019). *OEIS A329515: coordination sequences of honeycomb cylinders of odd width 2n+1*. URL: <https://oeis.org/A329515>.

*Commentary.*

The imported honeycomb distance is twice the TeaCoordinationSequence residual on A vertices and one plus twice that residual on B vertices. A geodesic of the potential length and the plane-distance identity give the quotient-distance bounds.

The offset translation changes s=i+j by 2n+1. Euclidean division gives a unique A representative with −n≤s≤n and a unique B representative with −n−1≤s≤n−1. The potential inequalities show these representatives minimize distance in each quotient class, including n=0.

At A-radius 2k with k>0, the shell count is 6k for k<n, 6n for k=n, and 4n+2 for k>n. At B-radius 2k+1 it is 6k+3 for k<n, 5n+2 for k=n, and 4n+2 for k>n; the radius-zero count is one. Thus positive radii are 3m before 2n+1, 5n+2 at 2n+1, and 4n+2 afterwards.

Comparing second differences of the integer-cast shell series gives exactly the displayed identity. C maps an integer to its constant power series; n−2 is formed after casting n to ℤ. Powers have natural exponents, and X lies in PowerSeries ℤ. At n=0 the source term x²x^(−1) is combined before clearing denominators. Since 1−X has constant coefficient one, it is a unit, so the displayed cleared identity is equivalent to the source expression. No convergence or physical realization is asserted.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.Cylinder`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.c`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.cylinderGraph`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.origin`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.result`
- Truth anchor: `D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination.translationSetoid`
- Dependency: [D5/S3/StatisticalMechanics/HoneycombCylinderCoordination](HoneycombCylinderCoordination.md)
- Dependency: [D5/S3/StatisticalMechanics/TeaCoordinationSequence](TeaCoordinationSequence.md)
