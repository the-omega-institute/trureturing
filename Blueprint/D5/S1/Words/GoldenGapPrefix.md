# Golden Gap Prefix Chain

## Abstract

Establish the adjacent-prefix chain for finite Fibonacci and golden gap words.

**Theorem 1.1 (Fibonacci words satisfy the append recurrence).**

$$\forall Q\in\mathbb{N},\ \operatorname{fibWord}(Q+2)=\operatorname{append}(\operatorname{fibWord}(Q+1), \operatorname{fibWord}(Q))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenGapPrefix.fibWord_append_rec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Fibonacci word at level Q plus two is the concatenation of the words at levels Q plus one and Q.

**Theorem 1.2 (Adjacent Fibonacci words form a prefix chain).**

$$\forall Q\in\mathbb{N},\ \operatorname{prefix}(\operatorname{fibWord}(Q), \operatorname{fibWord}(Q+1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenGapPrefix.fibWord_prefix_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite Fibonacci word is a prefix of the word at the next level.

**Theorem 1.3 (Adjacent golden gap words form a prefix chain).**

$$\forall Q\in\mathbb{N},\ Q\ge2\Rightarrow \operatorname{prefix}(\operatorname{goldenGapWord}(Q), \operatorname{goldenGapWord}(Q+1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenGapPrefix.goldenGapWord_prefix_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From level two onward, the frozen golden-gap tower identification transfers the Fibonacci prefix chain to consecutive golden gap words.

## References

- Truth anchor: `D5/S1/Words/GoldenGapPrefix.fibWord_append_rec`
- Truth anchor: `D5/S1/Words/GoldenGapPrefix.fibWord_prefix_succ`
- Truth anchor: `D5/S1/Words/GoldenGapPrefix.goldenGapWord_prefix_succ`
- Dependency: [D5/S0/Tower/GoldenGapWord](../../S0/Tower/GoldenGapWord.md)
