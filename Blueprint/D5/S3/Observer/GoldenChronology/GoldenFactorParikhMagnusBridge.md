# Golden factors through Parikh and Magnus coordinates

## Abstract

The actual binary Parikh matrix and represented step-two Chen signature determine a legal golden factor. Their first-degree entries supply length and counts; one central Magnus coordinate supplies the remaining second-order information.

Write W(n,i) for goldenFactor(n,i), R(i,n) for goldenWindowTrueCount(i,n), and B(i,n) for goldenTrueFalseCount(i,n). Write K(w) for scatteredTrueFalseCount(w), P(w) for binaryParikhMatrix(w), S(w) for chronologicalSignature(binaryLetterObservation,w), and C(w) for doubledMagnusDegreeTwo(S(w))(0,2). All lengths and starts are arbitrary naturals, and integer denotes the natural-to-integer cast.

**Theorem 1.1 (The word's actual true count).**

$$\forall n \in Nat,\; \forall i \in Nat,\; \operatorname{count}\left(\operatorname{W}\left(n, i\right), true\right) = \operatorname{R}\left(i, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/GoldenPalindromicFactorComplexity.goldenFactor_count_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The consecutive factor is the list of letters goldenWord(i+k) for k less than n. Counting its true letters gives exactly the canonical window count R(i,n). The false count is n minus R(i,n), because the two letter counts exhaust the length.

**Theorem 1.2 (The word's actual scattered-pair count).**

$$\forall n \in Nat,\; \forall i \in Nat,\; \operatorname{K}\left(\operatorname{W}\left(n, i\right)\right) = \operatorname{B}\left(i, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_scattered_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending the letter at i+n extends W(n,i) to W(n+1,i). A false letter contributes R(i,n) new ordered pairs and a true letter contributes none. Thus the arbitrary-word pair counter K agrees with the golden sum B at every length, including zero.

**Theorem 1.3 (The division-free golden center).**

$$\forall n \in Nat,\; \forall i \in Nat,\; \operatorname{C}\left(\operatorname{W}\left(n, i\right)\right) = 2 \cdot \operatorname{integer}\left(\operatorname{B}\left(i, n\right)\right) - \operatorname{integer}\left(\operatorname{R}\left(i, n\right)\right) \cdot \left(\operatorname{integer}\left(n\right) - \operatorname{integer}\left(\operatorname{R}\left(i, n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_doubled_magnus_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the actual word counts and pair count into the binary Magnus formula gives the displayed integer coordinate. The subtraction n minus R is performed in the integers after casting. The identity requires no positive-length or mixed-letter hypothesis.

**Theorem 1.4 (The Parikh matrix has exactly the word's fibers).**

$$\forall n \in Nat,\; \forall m \in Nat,\; \forall i \in Nat,\; \forall j \in Nat,\; \operatorname{W}\left(n, i\right) = \operatorname{W}\left(m, j\right) \Leftrightarrow \operatorname{P}\left(\operatorname{W}\left(n, i\right)\right) = \operatorname{P}\left(\operatorname{W}\left(m, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_eq_iff_parikh_matrix_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the matrices gives equality of both letter counts and of K. Summing the two counts recovers n=m, and the fixed-length binomial recovery theorem then recovers the complete word. The reverse implication follows by substituting equal words. The lengths n and m need not be assumed equal.

**Theorem 1.5 (First degree and center recover the word).**

$$\forall n \in Nat,\; \forall m \in Nat,\; \forall i \in Nat,\; \forall j \in Nat,\; \operatorname{degreeOne}\left(\operatorname{S}\left(\operatorname{W}\left(n, i\right)\right)\right) = \operatorname{degreeOne}\left(\operatorname{S}\left(\operatorname{W}\left(m, j\right)\right)\right) \Rightarrow \left(\operatorname{C}\left(\operatorname{W}\left(n, i\right)\right) = \operatorname{C}\left(\operatorname{W}\left(m, j\right)\right) \Rightarrow \operatorname{W}\left(n, i\right) = \operatorname{W}\left(m, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_eq_of_first_degree_and_magnus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the entire degreeOne matrices gives equality of their true and false entries. Together with equality of the one central doubled Magnus entry, it gives equal Parikh matrices and hence equal legal factors. Equality of the center alone is not the hypothesis here.

**Theorem 1.6 (The represented Chen signature has the same kernel).**

$$\forall n \in Nat,\; \forall m \in Nat,\; \forall i \in Nat,\; \forall j \in Nat,\; \operatorname{W}\left(n, i\right) = \operatorname{W}\left(m, j\right) \Leftrightarrow \operatorname{S}\left(\operatorname{W}\left(n, i\right)\right) = \operatorname{S}\left(\operatorname{W}\left(m, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_eq_iff_step_two_signature_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal signatures give equal first degree and equal center, so they give equal legal words. Equal words give equal signatures. These equivalences apply to word content, including the empty factor and pure-letter factors; they do not identify occurrence starts or attach prime labels to positions.

## References

- Truth anchor: `D5/S1/Words/Palindromes/GoldenPalindromicFactorComplexity.goldenFactor_count_true`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_doubled_magnus_center`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_eq_iff_parikh_matrix_eq`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_eq_iff_step_two_signature_eq`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_eq_of_first_degree_and_magnus`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_scattered_count`
- Dependency: [D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity](../../../S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.md)
- Dependency: [D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge](BinaryParikhStepTwoBridge.md)
