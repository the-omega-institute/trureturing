# The Infinite Golden Word

## Abstract

Construct the infinite golden word as the coherent diagonal limit of finite tower words.

**Theorem 1.1 (Finite Fibonacci words have Fibonacci length).**

$$\operatorname{length}(\operatorname{fibWord}(Q))=\operatorname{Fib}(Q+2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenWord.fibWord_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Zeckendorf realization of a level-Q word contains exactly Fib(Q+2) letters.

**Theorem 1.2 (Every diagonal index occurs at its own level).**

$$i<\operatorname{length}(\operatorname{fibWord}(i))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenWord.index_lt_diagonal_level` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fibonacci lower bound makes index i a valid position in fibWord(i), so the diagonal construction is total.

**Definition 1.3 (The golden word is read on the tower diagonal).**

Lean statement: `D5/S1/Words/GoldenWord.goldenWord`

*Formalization.* `D5/S1/Words/GoldenWord.goldenWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The letter at index i is the ith letter of the finite Fibonacci word at level i. This definition retains the finite tower as its construction.

**Theorem 1.4 (Every covering finite stage gives the same letter).**

$$\operatorname{goldenWord}(i)=\operatorname{get}(\operatorname{fibWord}(Q),i)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenWord.goldenWord_eq_fibWord_get` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding both the diagonal stage and an arbitrary covering stage into a common later word proves that their ith entries agree.

**Theorem 1.5 (Letters are characterized by the least Zeckendorf digit).**

$$\operatorname{goldenWord}(i)=true \iff \neg(2\in\operatorname{wdigits}(i))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenWord.goldenWord_char_zeckendorf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A golden-word letter is true exactly when the least Zeckendorf weight is absent. This is a theorem about the diagonal tower definition, not a replacement definition.

**Theorem 1.6 (Frozen golden-gap stages give the same letters).**

$$\operatorname{goldenWord}(i)=\operatorname{get}(\operatorname{goldenGapWord}(Q),i)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenWord.goldenWord_eq_goldenGapWord_get` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From level two onward, the frozen golden-gap identification transfers finite-stage coherence to the tower's gap words.

**Theorem 1.7 (Each frozen golden-gap word is a full finite prefix).**

$$\operatorname{prefix}(\operatorname{goldenWord},\operatorname{goldenGapWord}(Q))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenWord.goldenWord_prefix_eq_goldenGapWord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Collecting the coherent pointwise letters over the finite length recovers the entire frozen golden-gap word.

## References

- Truth anchor: `D5/S1/Words/GoldenWord.fibWord_length`
- Truth anchor: `D5/S1/Words/GoldenWord.goldenWord`
- Truth anchor: `D5/S1/Words/GoldenWord.goldenWord_char_zeckendorf`
- Truth anchor: `D5/S1/Words/GoldenWord.goldenWord_eq_fibWord_get`
- Truth anchor: `D5/S1/Words/GoldenWord.goldenWord_eq_goldenGapWord_get`
- Truth anchor: `D5/S1/Words/GoldenWord.goldenWord_prefix_eq_goldenGapWord`
- Truth anchor: `D5/S1/Words/GoldenWord.index_lt_diagonal_level`
- Dependency: [D5/S0/Tower/GoldenGapZeckendorf](../../S0/Tower/GoldenGapZeckendorf.md)
- Dependency: [D5/S1/Words/GoldenGapPrefix](GoldenGapPrefix.md)
