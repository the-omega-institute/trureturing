# All coordinate evaluation classes have the same size

## Abstract

An additive binary code containing the all-one word has uniform evaluation classes when every nonconstant word has half the code length.

**Theorem 1.1 (All coordinate evaluation classes have the same size).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCodeCoordinateClass.card_mul_coordinateClass_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCodeCoordinateClass.card_mul_coordinateClass_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be an additive binary code of length 2n, containing the all-one word and with weight n for every word other than zero and one. The size of each evaluation class times the size of K is 4n. Translation by the all-one word pairs both slices of the code. In the slice vanishing at a fixed coordinate, each coordinate outside its evaluation class takes the value one on half the slice. Counting these incidences by codewords and by coordinates determines the size of the class.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCodeCoordinateClass.card_mul_coordinateClass_card`
