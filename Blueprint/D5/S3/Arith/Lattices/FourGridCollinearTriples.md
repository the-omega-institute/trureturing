# Collinear Triples in the Four-Point Grid

## Abstract

Collinear triples in every finite Cartesian power of the four-point grid have an exact count.

The grid has four coordinates on each axis. Collinearity is expressed over the integers by the vanishing of every two-by-two minor, while cardinality three makes each counted subset unordered and distinct.

**Definition 1.1 (The four-point Cartesian grid).**

$$\forall d : \mathbb{N}, \operatorname{GridPoint}\left(d\right) = \operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(4\right)$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.GridPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point assigns one of the four values in Fin(4) to each of d coordinates.

**Definition 1.2 (Integral collinearity).**

$$\forall d : \mathbb{N}, \forall x , y , z : \operatorname{GridPoint}\left(d\right), \operatorname{Collinear}\left(x, y, z\right) \iff (\forall i , j : \operatorname{Fin}\left(d\right), \left(\operatorname{intCast}\left(\operatorname{val}\left(y(i)\right)\right) - \operatorname{intCast}\left(\operatorname{val}\left(x(i)\right)\right)\right) \cdot \left(\operatorname{intCast}\left(\operatorname{val}\left(z(j)\right)\right) - \operatorname{intCast}\left(\operatorname{val}\left(x(j)\right)\right)\right) = \left(\operatorname{intCast}\left(\operatorname{val}\left(y(j)\right)\right) - \operatorname{intCast}\left(\operatorname{val}\left(x(j)\right)\right)\right) \cdot \left(\operatorname{intCast}\left(\operatorname{val}\left(z(i)\right)\right) - \operatorname{intCast}\left(\operatorname{val}\left(x(i)\right)\right)\right))$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.Collinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every ordered pair of coordinates, the two displacement vectors have zero integral minor. Both coordinate binders range over Fin(d).

**Definition 1.3 (Unordered distinct collinear triples).**

$$\forall d : \mathbb{N}, \forall s : \operatorname{Finset}\left(\operatorname{GridPoint}\left(d\right)\right), \operatorname{IsCollinearTriple}\left(s\right) \iff (\operatorname{card}\left(s\right) = 3 \land \forall x \in s, \forall y \in s, \forall z \in s, \operatorname{Collinear}\left(x, y, z\right))$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.IsCollinearTriple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finset has exactly three elements, and every ordered selection of three members satisfies the integral minor equations.

**Definition 1.4 (The sequence count).**

$$\forall d : \mathbb{N}, \operatorname{matharCount}\left(d\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{IsCollinearTriple}, \operatorname{powersetCard}\left(3, ((\operatorname{univ} : \operatorname{Finset}\left(\operatorname{GridPoint}\left(d\right)\right)))\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.matharCount` (`✓ std3`).

*Citation.* Richard J. Mathar (2010). *OEIS A178294, Number of collinear point triples in a 4 X 4 X 4 X... n-dimensional cubic grid*. URL: <https://oeis.org/A178294>.

*Commentary.*

The count is the cardinality of the collinear members of powersetCard(3) applied to the full four-point d-grid.

**Definition 1.5 (Same-parity endpoint coordinates).**

$$\forall a , b : \operatorname{Fin}\left(4\right), \operatorname{SameParity}\left(a, b\right) \iff \operatorname{natMod}\left(\operatorname{val}\left(a\right), 2\right) = \operatorname{natMod}\left(\operatorname{val}\left(b\right), 2\right)$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.SameParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two natural representatives have equal remainders modulo two.

**Definition 1.6 (Decidability of same-parity coordinates).**

$$(\operatorname{DecidableRel}\left(SameParity\right))$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.instDecidableRelFinOfNatNatSameParity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard J. Mathar (2010). *OEIS A178294, Number of collinear point triples in a 4 X 4 X 4 X... n-dimensional cubic grid*. URL: <https://oeis.org/A178294>.

*Commentary.*

The anonymous instance command generates this auto-named declaration; unfolding SameParity reduces it to a decidable arithmetic condition.

**Definition 1.7 (Equal-or-extreme endpoint coordinates).**

$$\forall a , b : \operatorname{Fin}\left(4\right), \operatorname{EqualOrExtreme}\left(a, b\right) \iff (a = b \lor \operatorname{val}\left(a\right) = 0 \land \operatorname{val}\left(b\right) = 3 \lor \operatorname{val}\left(a\right) = 3 \land \operatorname{val}\left(b\right) = 0)$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.EqualOrExtreme` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A permitted pair is equal, zero-to-three, or three-to-zero.

**Definition 1.8 (Decidability of equal-or-extreme coordinates).**

$$(\operatorname{DecidableRel}\left(EqualOrExtreme\right))$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.instDecidableRelFinOfNatNatEqualOrExtreme` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard J. Mathar (2010). *OEIS A178294, Number of collinear point triples in a 4 X 4 X 4 X... n-dimensional cubic grid*. URL: <https://oeis.org/A178294>.

*Commentary.*

The anonymous instance command generates this auto-named declaration; unfolding EqualOrExtreme reduces it to decidable equality and arithmetic conditions.

**Definition 1.9 (Coordinatewise endpoint pairs).**

$$\forall relation : \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(4\right) \to \operatorname{Prop}, \forall d : \mathbb{N}, \operatorname{CoordinatePairs}\left(relation, d\right) = \{p : \operatorname{GridPoint}\left(d\right) \times \operatorname{GridPoint}\left(d\right) \mid \forall i : \operatorname{Fin}\left(d\right), relation(\operatorname{fst}\left(p\right)(i), \operatorname{snd}\left(p\right)(i))\}$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.CoordinatePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each ordered pair of grid points satisfies the supplied relation at every coordinate.

**Definition 1.10 (Distinct coordinatewise endpoint pairs).**

$$\forall relation : \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(4\right) \to \operatorname{Prop}, \forall d : \mathbb{N}, \operatorname{DistinctCoordinatePairs}\left(relation, d\right) = \{p : \operatorname{CoordinatePairs}\left(relation, d\right) \mid \operatorname{fst}\left(\operatorname{val}\left(p\right)\right) \neq \operatorname{snd}\left(\operatorname{val}\left(p\right)\right)\}$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.DistinctCoordinatePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This subtype removes exactly the diagonal endpoint pairs.

**Definition 1.11 (Integral midpoint coordinate).**

$$\forall a , b : \operatorname{Fin}\left(4\right), \operatorname{val}\left(\operatorname{midpointCoordinate}\left(a, b\right)\right) = \operatorname{natDiv}\left(\operatorname{val}\left(a\right) + \operatorname{val}\left(b\right), 2\right)$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.midpointCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value is natural division of the endpoint sum by two. Its bound below four supplies the dependent Fin(4) component.

**Definition 1.12 (Coordinatewise midpoint).**

$$\forall d : \mathbb{N}, \forall x , z : \operatorname{GridPoint}\left(d\right), \forall i : \operatorname{Fin}\left(d\right), \operatorname{midpoint}\left(x, z\right)(i) = \operatorname{midpointCoordinate}\left(x(i), z(i)\right)$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.midpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The point is obtained by applying midpointCoordinate independently on every axis.

**Definition 1.13 (Oriented arithmetic progressions).**

$$\forall d : \mathbb{N}, \operatorname{OrientedArithmeticProgression}\left(d\right) = \{t : \operatorname{GridPoint}\left(d\right) \times (\operatorname{GridPoint}\left(d\right) \times \operatorname{GridPoint}\left(d\right)) \mid \operatorname{fst}\left(t\right) \neq \operatorname{snd}\left(\operatorname{snd}\left(t\right)\right) \land \forall i : \operatorname{Fin}\left(d\right), \operatorname{intCast}\left(\operatorname{val}\left(\operatorname{fst}\left(t\right)(i)\right)\right) + \operatorname{intCast}\left(\operatorname{val}\left(\operatorname{snd}\left(\operatorname{snd}\left(t\right)\right)(i)\right)\right) = 2 \cdot \operatorname{intCast}\left(\operatorname{val}\left(\operatorname{fst}\left(\operatorname{snd}\left(t\right)\right)(i)\right)\right)\}$$

*Formalization.* `D5/S3/Arith/Lattices/FourGridCollinearTriples.OrientedArithmeticProgression` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The endpoints differ, and their coordinatewise integral sum is twice the middle point.

**Theorem 1.14 (Counts of the two endpoint-code families).**

$$\forall d : \mathbb{N}, \operatorname{card}\left(\operatorname{DistinctCoordinatePairs}\left(\operatorname{SameParity}, d\right)\right) = 8^{d} - 4^{d} \land \operatorname{card}\left(\operatorname{DistinctCoordinatePairs}\left(\operatorname{EqualOrExtreme}, d\right)\right) = 6^{d} - 4^{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/FourGridCollinearTriples.endpoint_pair_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are 8^d same-parity coordinate pairs and 6^d equal-or-extreme pairs. Removing the 4^d diagonal pairs gives both displayed conjuncts.

**Theorem 1.15 (Count of oriented arithmetic progressions).**

$$\forall d : \mathbb{N}, \operatorname{card}\left(\operatorname{OrientedArithmeticProgression}\left(d\right)\right) = 8^{d} - 4^{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/FourGridCollinearTriples.oriented_arithmetic_progression_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A same-parity ordered endpoint pair has one integral midpoint, and every oriented nonconstant arithmetic progression recovers its endpoint pair.

**Theorem 1.16 (Mathar's closed form).**

$$\forall d : \mathbb{N}, 2 \cdot \operatorname{matharCount}\left(d\right) = 8^{d} + 2 \cdot 6^{d} - 3 \cdot 4^{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/FourGridCollinearTriples.mathar_collinear_triples` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a178294-four-grid-collinear-triples` (proved) by `D5/S3/Arith/Lattices/FourGridCollinearTriples.mathar_collinear_triples`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a178294-four-grid-collinear-triples","declaration_gid":"D5/S3/Arith/Lattices/FourGridCollinearTriples.mathar_collinear_triples","resolution_kind":"proved"} -->

*Citation.* Richard J. Mathar (2010). *OEIS A178294, Number of collinear point triples in a 4 X 4 X 4 X... n-dimensional cubic grid*. URL: <https://oeis.org/A178294>.

*Commentary.*

Marked collinear triples split bijectively into oriented arithmetic progressions and two orientations of the equal-or-extreme endpoint codes. Cardinality transfer and the two preceding counts give the identity. The subtraction on the right is natural-number truncated subtraction, exactly as written.

## References

- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.Collinear`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.CoordinatePairs`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.DistinctCoordinatePairs`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.EqualOrExtreme`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.GridPoint`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.IsCollinearTriple`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.OrientedArithmeticProgression`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.SameParity`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.endpoint_pair_counts`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.instDecidableRelFinOfNatNatEqualOrExtreme`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.instDecidableRelFinOfNatNatSameParity`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.matharCount`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.mathar_collinear_triples`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.midpoint`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.midpointCoordinate`
- Truth anchor: `D5/S3/Arith/Lattices/FourGridCollinearTriples.oriented_arithmetic_progression_count`
