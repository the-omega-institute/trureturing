# Golden Gap Word

## Abstract

The full golden tower gap word is the Fibonacci substitution word.

The boundary-completed gap list carries more information than its two multiplicities: it records every large and small gap in the frozen Fin order. Refinement turns this ordered list into a Fibonacci word.

**Definition 1.1 (Oriented Fibonacci replacement).**

Lean statement: `D5/S0/Tower/GoldenGapWord.subst`

*Formalization.* `D5/S0/Tower/GoldenGapWord.subst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A large letter is replaced by large then small, while a small letter is replaced by one large letter.

**Definition 1.2 (Finite Fibonacci word).**

Lean statement: `D5/S0/Tower/GoldenGapWord.fibWord`

*Formalization.* `D5/S0/Tower/GoldenGapWord.fibWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting from one large letter, fibWord iterates the oriented replacement once per level.

**Definition 1.3 (Boundary-completed golden gap word).**

Lean statement: `D5/S0/Tower/GoldenGapWord.goldenGapWord`

*Formalization.* `D5/S0/Tower/GoldenGapWord.goldenGapWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This word is defined directly by List.ofFn over Fin(Fib(Q+2)). Each letter tests GoldenGapFrequency.fullGap at that exact index, so the last interval from the final name value to one is part of the word.

**Lemma 1.4 (A false letter is the small gap).**

$$\operatorname{gapLetter}\left(Q, i\right) = \mathit{false} \Leftrightarrow \operatorname{fullGap}\left(Q, i\right) = \operatorname{smallGapLength}\left(Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenGapWord.golden_gap_false_iff_small` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-length spectrum rules out a third case: failing the large-gap test is equivalent to having the frozen small length.

**Theorem 1.5 (Refinement substitutes the complete word).**

$$\forall Q \in N,\; Q \ge 2 \Rightarrow \operatorname{flatMap}\left(\operatorname{goldenGapWord}\left(Q\right), \mathit{subst}\right) = \operatorname{goldenGapWord}\left(Q + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenGapWord.golden_gap_word_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality is global and positional. The proof splits the complete fine Fin interval into its two Fibonacci blocks and proves the fullGap scaling on each block; the final upper-block index is the terminal boundary gap, so no suffix is omitted.

**Theorem 1.6 (The full gap word is Fibonacci).**

$$\forall Q \in N,\; Q \ge 2 \Rightarrow \operatorname{goldenGapWord}\left(Q\right) = \operatorname{fibWord}\left(Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenGapWord.golden_full_gap_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From level two onward the word cut directly from the frozen tower is the recursively generated Fibonacci word. This is repo-derived new reasoning: the frozen frequency theorem follows mathematically by counting letters, but that module and its ledger node remain unchanged.

## References

- Truth anchor: `D5/S0/Tower/GoldenGapWord.fibWord`
- Truth anchor: `D5/S0/Tower/GoldenGapWord.goldenGapWord`
- Truth anchor: `D5/S0/Tower/GoldenGapWord.golden_full_gap_word`
- Truth anchor: `D5/S0/Tower/GoldenGapWord.golden_gap_false_iff_small`
- Truth anchor: `D5/S0/Tower/GoldenGapWord.golden_gap_word_step`
- Truth anchor: `D5/S0/Tower/GoldenGapWord.subst`
- Dependency: [D5/S0/Tower/GoldenGapFrequency](GoldenGapFrequency.md)
