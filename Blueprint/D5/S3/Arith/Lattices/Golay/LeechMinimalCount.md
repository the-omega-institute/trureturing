# The complete integer minimum sphere

## Abstract

The complete integer minimum sphere

The sphere contains all integer-valued functions on Fin 24 satisfying the original Golay congruences and square sum 32; its domain is unbounded. Even vectors have either two coordinates of absolute value four, or a Golay octad of coordinates of absolute value two with even minus-sign parity. Odd vectors have one coordinate of absolute value three and twenty-three unit coordinates, determined by a distinguished position and an actual Golay codeword. The family sizes are 1104, 97152 and 98304. The rational function scaledSquare is squareSum divided by eight. This coordinate classification supplies no real self-duality, unimodular Gram realization, uniqueness theorem, VOA dimension, Monster representation or string-theory construction.

**Theorem 1.1 (Every unbounded sphere vector has a family).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.familyVector_surjective_on_sphere`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.familyVector_surjective_on_sphere` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every element x of the actual admissible integer square-sum-32 sphere is familyVector p for some p in the disjoint union of the two-support, even-signed-octad and distinguished-position codeword families. The congruence representation determines parity; the square-sum bound and code minimum force each possible coordinate shape. No coordinate box or classification premise is imposed.

**Definition 1.2 (A bijection with the three families).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.sphereEquiv`

*Formalization.* `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.sphereEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete disjoint family type is equivalent to the subtype of admissible integer vectors with square sum 32. Every constructed vector satisfies the congruences and square sum. The support, quotient residue, exceptional odd coordinate and sign parity distinguish the families and recover their parameters.

**Theorem 1.3 (Actual finiteness of the sphere).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.shortest_vectors_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.shortest_vectors_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full subtype of admissible functions Fin 24 to the integers with square sum 32 is finite, by equivalence with the three finite parameter families. Finiteness is derived on the original unbounded domain.

**Theorem 1.4 (The classical count 196560).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.shortest_vectors_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.shortest_vectors_card` (`✓ std3`). ∎

*Citation.* Gabriele Nebe and Neil J. A. Sloane (2014). *The Lattice LAMBDA24 (The Leech Lattice)*. URL: <https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/Leech.html>.

*Commentary.*

The cardinality of all admissible integer vectors of square sum 32 is 196560. The counts are binomial(24,2) times four for the two-support family, 759 times 128 for the signed octads, and 24 times 4096 for the odd family. The code cardinality and octad count are proved properties of the original encoder image, not new premises.

**Theorem 1.5 (The literal rational squared-length-four sphere).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.scaled_shortest_vectors_finite_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.scaled_shortest_vectors_finite_card` (`✓ std3`). ∎

*Citation.* Gabriele Nebe and Neil J. A. Sloane (2014). *The Lattice LAMBDA24 (The Leech Lattice)*. URL: <https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/Leech.html>.

*Commentary.*

The subtype of admissible integer vectors with scaledSquare equal to four is finite and has cardinality 196560. Here scaledSquare is exactly squareSum divided by eight in the rationals. The identity map on vectors is a two-sided equivalence with square sum 32. No real lattice or operator-state realization is assumed or supplied.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.familyVector_surjective_on_sphere`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.scaled_shortest_vectors_finite_card`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.shortest_vectors_card`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.shortest_vectors_finite`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechMinimalCount.sphereEquiv`
- Dependency: [D5/S3/Arith/Lattices/Golay/GolayOctadCount](GolayOctadCount.md)
- Dependency: [D5/S3/Arith/Lattices/Golay/LeechSignedSupport](LeechSignedSupport.md)
