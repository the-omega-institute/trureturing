# D-Bonacci Gap Alphabet

## Abstract

Finite d-bonacci gap letters carry the exact local refinement substitution.

The gap labels zero through d minus one form a finite alphabet. Zero is replaced by the top letter; every successor is replaced by the top letter followed by its predecessor.

**Definition 1.1 (Finite gap alphabet).**

$$\operatorname{GapLetter}\left(d\right) = \operatorname{Fin}\left(d\right)$$

*Formalization.* `D5/S0/Tower/DBonacci/GapAlphabet.DBonacciGapLetter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Using Fin d makes the allowed label bound part of the type.

**Definition 1.2 (Gap-letter substitution).**

$$\operatorname{substitute}\left(d, \mathit{letter}\right) = \operatorname{zeroOrSuccessorReplacement}\left(d, \mathit{letter}\right)$$

*Formalization.* `D5/S0/Tower/DBonacci/GapAlphabet.gapLetterSubstitution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The replacement stays in Fin d: its first letter is d minus one, and a nonzero input contributes its predecessor second.

**Theorem 1.3 (General typed gap substitution).**

$$\forall i \in \operatorname{coarseGapIndex}\left(d, Q\right),\; \operatorname{refinementWord}\left(d, Q, i\right) = \operatorname{substitute}\left(d, \operatorname{coarseGapLetter}\left(d, Q, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/GapAlphabet.dbonacci_gap_letter_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d at least two, the existing local metric theorem supplies the coarse letter and proves that the fine interval realizes precisely its one- or two-letter replacement word.

**Theorem 1.4 (Order-three substitution equality).**

$$\forall letter \in \operatorname{Fin}\left(3\right),\; \operatorname{mapToTribonacci}\left(\operatorname{substitute}\left(3, \mathit{letter}\right)\right) = \operatorname{tribonacciSubstitute}\left(\operatorname{mapToTribonacci}\left(\mathit{letter}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/GapAlphabet.dbonacciGapLetterSubstitution_three_eq_tribonacciGapLetterSubstitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence sends labels zero, one, and two to small, combined, and large. Transporting the typed substitution across it gives the frozen Tribonacci substitution exactly.

**Theorem 1.5 (Order-three geometric consistency).**

$$\forall i \in \operatorname{coarseGapIndex}\left(3, Q\right),\; \operatorname{transportedRefinementWord}\left(Q, i\right) = \operatorname{tribonacciSubstitute}\left(\operatorname{transportedCoarseLetter}\left(Q, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/GapAlphabet.dbonacci_gap_letter_substitution_three_consistent_with_tribonacci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This corollary takes the witness produced by the general geometric theorem and proves that its transported word is the frozen replacement word, so the specialization is not a second source.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/GapAlphabet.DBonacciGapLetter`
- Truth anchor: `D5/S0/Tower/DBonacci/GapAlphabet.dbonacciGapLetterSubstitution_three_eq_tribonacciGapLetterSubstitution`
- Truth anchor: `D5/S0/Tower/DBonacci/GapAlphabet.dbonacci_gap_letter_substitution`
- Truth anchor: `D5/S0/Tower/DBonacci/GapAlphabet.dbonacci_gap_letter_substitution_three_consistent_with_tribonacci`
- Truth anchor: `D5/S0/Tower/DBonacci/GapAlphabet.gapLetterSubstitution`
- Dependency: [D5/S0/Tower/DBonacci/Substitution](Substitution.md)
- Dependency: [D5/S0/Tower/Tribonacci/Substitution](../Tribonacci/Substitution.md)
