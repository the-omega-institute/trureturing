# Binary Parikh matrices and step-two Chen coordinates

## Abstract

An ordered product of binary unipotent matrices records the two letter counts and the scattered true-before-false count. The same counts determine the represented step-two Chen signature and its doubled Magnus center.

**Definition 1.1 (The integer matrix algebra).**

$$M_{3} = \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), Int\right)$$

*Formalization.* `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.IntegerMatrix3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M with subscript three denotes IntegerMatrix3, the algebra of three-by-three integer matrices with rows and columns indexed by zero, one and two. Write matrixUnit(a,b) for the matrix whose sole nonzero entry is one at (a,b).

**Definition 1.2 (Nilpotent letter observations).**

$$\forall b \in Bool,\; \operatorname{binaryLetterObservation}\left(b\right) = \operatorname{if}\left(b, \operatorname{matrixUnit}\left(0, 1\right), \operatorname{matrixUnit}\left(1, 2\right)\right)$$

*Formalization.* `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binaryLetterObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A true letter contributes the matrix unit at (0,1); a false letter contributes the unit at (1,2). Multiplication in that order produces the unit at (0,2), whereas the reverse product is zero. Each individual letter matrix has square zero.

**Definition 1.3 (The ordered scattered-pair counter).**

$$\operatorname{K}\left([]\right) = 0 \land \left(\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{K}\left(\operatorname{cons}\left(true, w\right)\right) = \operatorname{count}\left(w, false\right) + \operatorname{K}\left(w\right) \land \operatorname{K}\left(\operatorname{cons}\left(false, w\right)\right) = \operatorname{K}\left(w\right)\right)$$

*Formalization.* `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.scatteredTrueFalseCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K(w) abbreviates scatteredTrueFalseCount(w). It counts pairs of positions with an earlier true letter and a later false letter, allowing any intervening letters. A leading true pairs with every false in the tail; a leading false contributes no new such pair.

**Theorem 1.4 (Appending a letter).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall b \in Bool,\; \operatorname{K}\left(\operatorname{append}\left(w, [b]\right)\right) = \operatorname{K}\left(w\right) + \operatorname{if}\left(b = true, 0, \operatorname{count}\left(w, true\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.scattered_true_false_count_append_letter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending true adds no true-before-false pair. Appending false adds one pair for every true already in the word. The formula includes the empty word.

**Theorem 1.5 (The two counts exhaust length).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{count}\left(w, true\right) + \operatorname{count}\left(w, false\right) = \operatorname{length}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_letter_counts_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every position of a binary word is either true or false. Thus the two natural counts sum to its length, including length zero.

**Definition 1.6 (The ordered unipotent product).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{P}\left(w\right) = \prod_{k\in \operatorname{range}\left(\operatorname{length}\left(w\right)\right)}(1 + \operatorname{binaryLetterObservation}\left(\operatorname{get}\left(w, k\right)\right))$$

*Formalization.* `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binaryParikhMatrix` (`✓ std3`).

*Citation.* Alexandru Mateescu; Arto Salomaa; Kai Salomaa; Sheng Yu (2001). *A sharpening of the Parikh mapping*. DOI: [10.1051/ita:2001131](https://doi.org/10.1051/ita:2001131). URL: <https://www.numdam.org/item/ITA_2001__35_6_551_0/>.

*Commentary.*

P(w) abbreviates binaryParikhMatrix(w). The product is taken from left to right in word order, and one is the identity matrix. The empty product is the identity. With r and f the true and false counts, its diagonal entries are one, its lower entries are zero, and its upper entries (0,1), (1,2), (0,2) are r, f, K. Multiplying two such matrices adds the counts and adds the cross term r times the second word's false count to K.

**Theorem 1.7 (The three Parikh entries).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{P}\left(w\right)\left(0, 1\right) = \operatorname{integer}\left(\operatorname{count}\left(w, true\right)\right) \land \left(\operatorname{P}\left(w\right)\left(1, 2\right) = \operatorname{integer}\left(\operatorname{count}\left(w, false\right)\right) \land \operatorname{P}\left(w\right)\left(0, 2\right) = \operatorname{integer}\left(\operatorname{K}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_parikh_matrix_entries` (`✓ std3`). ∎

*Citation.* Alexandru Mateescu; Arto Salomaa; Kai Salomaa; Sheng Yu (2001). *A sharpening of the Parikh mapping*. DOI: [10.1051/ita:2001131](https://doi.org/10.1051/ita:2001131). URL: <https://www.numdam.org/item/ITA_2001__35_6_551_0/>.

*Commentary.*

The displayed counts are cast from the naturals to the integers. The central matrix entry retains ordered scattered pairs, rather than adjacent transitions.

**Theorem 1.8 (The represented Chen entries).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{degreeOne}\left(\operatorname{S}\left(w\right)\right)\left(0, 1\right) = \operatorname{integer}\left(\operatorname{count}\left(w, true\right)\right) \land \left(\operatorname{degreeOne}\left(\operatorname{S}\left(w\right)\right)\left(1, 2\right) = \operatorname{integer}\left(\operatorname{count}\left(w, false\right)\right) \land \operatorname{doubledDegreeTwo}\left(\operatorname{S}\left(w\right)\right)\left(0, 2\right) = 2 \cdot \operatorname{integer}\left(\operatorname{K}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_step_two_signature_entries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

S(w) denotes chronologicalSignature(binaryLetterObservation,w). Its degreeOne matrix has the true and false counts at (0,1) and (1,2), and zero elsewhere. Its doubledDegreeTwo matrix has 2K at (0,2) and zero elsewhere. Chen composition gives the same cross term as the unipotent product; the degree-two convention is factorial, so it has no division.

**Theorem 1.9 (The doubled central Magnus coordinate).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{doubledMagnusDegreeTwo}\left(\operatorname{chronologicalSignature}\left(\mathrm{binaryLetterObservation}, w\right)\right)\left(0, 2\right) = 2 \cdot \operatorname{integer}\left(\operatorname{K}\left(w\right)\right) - \operatorname{integer}\left(\operatorname{count}\left(w, true\right)\right) \cdot \operatorname{integer}\left(\operatorname{count}\left(w, false\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_doubled_magnus_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

C(w) denotes the (0,2) entry of doubledMagnusDegreeTwo(S(w)). Subtracting the square of degreeOne from doubledDegreeTwo gives 2K minus the product of the letter counts. This statement holds for every binary word, including empty and pure-letter words, whose center is zero.

**Theorem 1.10 (Counts and center recover the matrix).**

$$\forall a \in \operatorname{List}\left(Bool\right),\; \forall b \in \operatorname{List}\left(Bool\right),\; \operatorname{count}\left(a, true\right) = \operatorname{count}\left(b, true\right) \Rightarrow \left(\operatorname{count}\left(a, false\right) = \operatorname{count}\left(b, false\right) \Rightarrow \left(\operatorname{C}\left(a\right) = \operatorname{C}\left(b\right) \Rightarrow \operatorname{P}\left(a\right) = \operatorname{P}\left(b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_parikh_eq_of_counts_and_magnus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two arbitrary words have the same true count, false count and doubled central Magnus entry, their pair counts agree by the integral center formula, and hence their complete Parikh matrices agree. This recovers the matrix; different ordered words can still have the same matrix.

## References

- Truth anchor: `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.IntegerMatrix3`
- Truth anchor: `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binaryLetterObservation`
- Truth anchor: `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binaryParikhMatrix`
- Truth anchor: `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_doubled_magnus_center`
- Truth anchor: `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_letter_counts_length`
- Truth anchor: `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_parikh_eq_of_counts_and_magnus`
- Truth anchor: `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_parikh_matrix_entries`
- Truth anchor: `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_step_two_signature_entries`
- Truth anchor: `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.scatteredTrueFalseCount`
- Truth anchor: `D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.scattered_true_false_count_append_letter`
- Dependency: [D5/S3/Observer/Chronology/StepTwoChronologicalSignature](../Chronology/StepTwoChronologicalSignature.md)
