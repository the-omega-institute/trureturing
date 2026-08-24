# Residue Coordinate Dimension

## Abstract

Three prime-power residue coordinates on ZMod 30 have minimum complete coordinate count three.

**Lemma 1.1 (The coordinate at two has modulus two).**

$$\operatorname{coordinateModulus}\left(q2\right) = 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q2_modulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate indexed by the prime two records residues modulo two. The exponent of two in thirty is one, so its associated prime-power modulus is exactly two.

**Lemma 1.2 (The coordinate at three has modulus three).**

$$\operatorname{coordinateModulus}\left(q3\right) = 3.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q3_modulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate indexed by the prime three records residues modulo three. Since thirty contains only one factor of three, the coordinate modulus is three.

**Lemma 1.3 (The coordinate at five has modulus five).**

$$\operatorname{coordinateModulus}\left(q5\right) = 5.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q5_modulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate indexed by the prime five records residues modulo five. The factor five occurs once in thirty, so the attached prime-power modulus is five.

**Lemma 1.4 (CRT readings preserve natural-number residues).**

$$\forall q: Coordinate, n: \mathbb{N},\ \operatorname{reading}\left(q, \operatorname{residue}\left(n, 30\right)\right) = \operatorname{residue}\left(n, \operatorname{coordinateModulus}\left(q\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.reading_natCast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading the residue class of a natural number at any coordinate returns the residue class of the same number at that coordinate's prime-power modulus. This is the natural-cast compatibility of the Chinese remainder equivalence.

**Lemma 1.5 (CRT readings preserve zero).**

$$\forall q: Coordinate, \operatorname{reading}\left(q, 0\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.reading_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coordinate sends the zero state modulo thirty to zero in its prime-power residue ring. This is the zero-preservation law for the Chinese remainder ring equivalence.

**Lemma 1.6 (The two-three readings merge fifteen and twenty-one).**

$$\operatorname{Merges}\left(\{q2, q3\}, 15, 21\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q2_q3_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The states fifteen and twenty-one are distinct modulo thirty, but they have the same residues modulo two and modulo three. The coordinate pair consisting of q2 and q3 therefore cannot distinguish them.

**Lemma 1.7 (The two-five readings merge zero and ten).**

$$\operatorname{Merges}\left(\{q2, q5\}, 0, 10\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q2_q5_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero and ten are different states modulo thirty while agreeing modulo both two and five. Consequently the q2 and q5 readings merge this explicit pair.

**Lemma 1.8 (The three-five readings merge zero and fifteen).**

$$\operatorname{Merges}\left(\{q3, q5\}, 0, 15\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q3_q5_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero and fifteen are distinct modulo thirty yet have equal residues modulo three and modulo five. Thus the q3 and q5 coordinate pair is also incomplete.

**Lemma 1.9 (Merging persists under coordinate restriction).**

$$\forall s, t: \operatorname{Finset}\left(Coordinate\right), \forall x, y: \operatorname{ZMod}\left(30\right),\ (s \subseteq t \land \operatorname{Merges}\left(t, x, y\right)) \Rightarrow \operatorname{Merges}\left(s, x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.merges_of_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a larger coordinate set gives identical joint readings for two distinct states, any subset gives identical readings for the same pair. Restricting an equal coordinate tuple cannot recover information that the larger tuple already lost.

**Lemma 1.10 (Every coordinate is two, three, or five).**

$$\forall q: Coordinate, q = q2 \lor q = q3 \lor q = q5.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.coordinate_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coordinate is a prime factor of thirty. The only such primes are two, three, and five, so the coordinate type has exactly these three possibilities.

**Lemma 1.11 (Fewer than three coordinates are incomplete).**

$$\forall s: \operatorname{Finset}\left(Coordinate\right), \operatorname{card}\left(s\right) < 3 \Rightarrow \neg \operatorname{Complete}\left(s\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.fewer_than_three_incomplete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any selection of fewer than three coordinates omits at least one of q2, q3, and q5. According to which coordinate is absent, the selection lies inside one of the three colliding pairs above; the subset principle then supplies two states it cannot separate.

**Lemma 1.12 (All three coordinates are complete).**

$$\operatorname{Complete}\left(univ\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.all_coordinates_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full coordinate family records all prime-power components of a state modulo thirty. Equality of every selected reading is therefore equality under the complete Chinese remainder equivalence, whose injectivity forces the original states to agree.

**Lemma 1.13 (A finite complete coordinate set exists).**

$$\exists n: \mathbb{N}, \exists s: \operatorname{Finset}\left(Coordinate\right),\ \operatorname{card}\left(s\right) = n \land \operatorname{Complete}\left(s\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.complete_coordinate_set_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit set containing q2, q3, and q5 has cardinality three. Because these are all coordinates, it is the full coordinate set and is complete by Chinese remainder injectivity.

**Theorem 1.14 (The residue-coordinate dimension is three).**

$$\operatorname{statisticalDimension} = 3.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.statistical_dimension_eq_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Statistical dimension is the least cardinality of a complete finite coordinate selection. The three-coordinate selection gives the upper bound, while every smaller selection is incomplete, so the least complete cardinality is exactly three.

The three pairwise collision witnesses establish minimality, and the full Chinese remainder reading establishes attainability. The result is therefore an exact dimension statement rather than only a bound.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.all_coordinates_complete`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.complete_coordinate_set_exists`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.coordinate_cases`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.fewer_than_three_incomplete`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.merges_of_subset`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q2_modulus`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q2_q3_collision`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q2_q5_collision`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q3_modulus`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q3_q5_collision`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.q5_modulus`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.reading_natCast`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.reading_zero`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.statistical_dimension_eq_three`
