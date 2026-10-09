# Magnus center, reversal and the exact length-parity boundary

## Abstract

At every fixed even length the central doubled Magnus coordinate determines a golden factor. At every odd length two distinct legal factors have center zero. Every same-length center fiber contains at most two word contents.

Write M(w) for magnusCenter(w), K(w) for scatteredTrueFalseCount(w), W(n,i) for goldenFactor(n,i), and R(i,n) for goldenWindowTrueCount(i,n). The words are finite binary lists; n and the occurrence starts are arbitrary naturals. All arithmetic in the center is integral, and integer denotes the natural-to-integer cast.

**Definition 1.1 (The actual represented center).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{M}\left(w\right) = \operatorname{doubledMagnusDegreeTwo}\left(\operatorname{chronologicalSignature}\left(\mathrm{binaryLetterObservation}, w\right)\right)\left(0, 2\right)$$

*Formalization.* `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.magnusCenter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation maps true to the matrix unit at (0,1) and false to that at (1,2). M is the (0,2) entry of the doubled second Magnus coordinate of this fixed chronological signature.

**Theorem 1.2 (The difference of oriented pair counts).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{M}\left(w\right) = 2 \cdot \operatorname{integer}\left(\operatorname{K}\left(w\right)\right) - \operatorname{integer}\left(\operatorname{count}\left(w, true\right)\right) \cdot \operatorname{integer}\left(\operatorname{count}\left(w, false\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.magnus_center_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice the true-before-false count minus the product of both letter counts is the true-before-false count minus the false-before-true count. The doubled convention avoids a half-integral coordinate.

**Theorem 1.3 (Reversal accounts for all unlike-letter pairs).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{K}\left(w\right) + \operatorname{K}\left(\operatorname{reverse}\left(w\right)\right) = \operatorname{count}\left(w, true\right) \cdot \operatorname{count}\left(w, false\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.scattered_pair_reversal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every choice of one true position and one false position has exactly one of the two orientations. Reversal interchanges those orientations, so the two scattered-pair counts sum to the product of the letter counts.

**Theorem 1.4 (Reversal negates the center).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{M}\left(\operatorname{reverse}\left(w\right)\right) = -\operatorname{M}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.magnus_center_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversal preserves the two letter counts and replaces K by their product minus K. Substitution into the center formula changes its sign.

**Theorem 1.5 (A palindrome has center zero).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{reverse}\left(w\right) = w \Rightarrow \operatorname{M}\left(w\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.magnus_center_zero_of_reverse_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A word equal to its reverse has M equal to minus M, hence M=0 over the integers. The empty word and one-letter words are included. Zero center alone does not assert that a word is a palindrome.

**Theorem 1.6 (One count and center at a known length).**

$$\forall n \in Nat,\; \forall i \in Nat,\; \forall j \in Nat,\; \operatorname{R}\left(i, n\right) = \operatorname{R}\left(j, n\right) \Rightarrow \left(\operatorname{M}\left(\operatorname{W}\left(n, i\right)\right) = \operatorname{M}\left(\operatorname{W}\left(n, j\right)\right) \Rightarrow \operatorname{W}\left(n, i\right) = \operatorname{W}\left(n, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.golden_factor_eq_of_count_and_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two golden factors of the same specified length, equal true counts and equal centers force equal scattered-pair counts. Fixed-length second-order recovery then gives equal words.

**Theorem 1.7 (Even length makes the count redundant).**

$$\forall n \in Nat,\; \operatorname{Even}\left(n\right) \Rightarrow \left(\forall i \in Nat,\; \forall j \in Nat,\; \operatorname{M}\left(\operatorname{W}\left(n, i\right)\right) = \operatorname{M}\left(\operatorname{W}\left(n, j\right)\right) \Rightarrow \operatorname{W}\left(n, i\right) = \operatorname{W}\left(n, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.even_length_center_recovers_golden_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Golden balance bounds the difference of the two true counts by one. If the counts differ by one, the two products r(n-r) differ by an odd integer when n is even, whereas twice the difference of the pair counts is even. Equal centers therefore force equal true counts, and count-plus-center recovery applies.

**Theorem 1.8 (A collision at every odd length).**

$$\forall n \in Nat,\; \operatorname{Odd}\left(n\right) \Rightarrow \left(\exists i \in Nat,\; \exists j \in Nat,\; \operatorname{W}\left(n, i\right) \ne \operatorname{W}\left(n, j\right) \land \left(\operatorname{M}\left(\operatorname{W}\left(n, i\right)\right) = 0 \land \operatorname{M}\left(\operatorname{W}\left(n, j\right)\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.odd_length_center_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each odd natural length the golden language has exactly two distinct palindromic factors. Both are reversal-fixed and therefore have center zero. Choosing occurrence starts for these two words gives the displayed collision. The statement asserts distinct word contents, without a prescribed distance between the starts.

**Theorem 1.9 (Center recovery holds exactly at even lengths).**

$$\forall n \in Nat,\; \left(\forall i \in Nat,\; \forall j \in Nat,\; \operatorname{M}\left(\operatorname{W}\left(n, i\right)\right) = \operatorname{M}\left(\operatorname{W}\left(n, j\right)\right) \Rightarrow \operatorname{W}\left(n, i\right) = \operatorname{W}\left(n, j\right)\right) \Leftrightarrow \operatorname{Even}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.center_recovers_fixed_length_iff_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recovery property quantifies over every pair of starts at the specified length. The even theorem proves one direction; the odd collision refutes the property at every odd length. Length zero is even: all its factors are empty and recovery holds. Length one is odd: the two one-letter factors both have center zero.

**Theorem 1.10 (No fiber has three distinct word contents).**

$$\forall n \in Nat,\; \forall i \in Nat,\; \forall j \in Nat,\; \forall k \in Nat,\; \operatorname{M}\left(\operatorname{W}\left(n, i\right)\right) = \operatorname{M}\left(\operatorname{W}\left(n, j\right)\right) \Rightarrow \left(\operatorname{M}\left(\operatorname{W}\left(n, i\right)\right) = \operatorname{M}\left(\operatorname{W}\left(n, k\right)\right) \Rightarrow \left(\operatorname{W}\left(n, i\right) = \operatorname{W}\left(n, j\right) \lor \left(\operatorname{W}\left(n, i\right) = \operatorname{W}\left(n, k\right) \lor \operatorname{W}\left(n, j\right) = \operatorname{W}\left(n, k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.center_fiber_has_at_most_two_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three factors of one length with a common center have pairwise true counts differing by at most one. Among three natural counts with that bound, two coincide. Their common count and center imply equal words, giving the displayed three-way disjunction. The bound holds at every length; odd zero-center fibers attain two, while every even fiber has at most one. None of these results recovers an absolute occurrence index, and this parity refers to word length.

## References

- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.center_fiber_has_at_most_two_words`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.center_recovers_fixed_length_iff_even`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.even_length_center_recovers_golden_factor`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.golden_factor_eq_of_count_and_center`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.magnusCenter`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.magnus_center_formula`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.magnus_center_reverse`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.magnus_center_zero_of_reverse_eq`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.odd_length_center_collision`
- Truth anchor: `D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.scattered_pair_reversal_sum`
- Dependency: [D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge](GoldenFactorParikhMagnusBridge.md)
