# Paid Dense Clause Word Conversion

## Abstract

A fixed finite word machine densely names every appearing variable and preserves the ordinary clause count.

**Theorem 1.1 (Total raw words, clean finite execution and assignment transport).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{denseMachine}\right), \operatorname{initList}\left(\mathit{denseMachine}, w\right), \operatorname{some}\left(\operatorname{haltList}\left(\mathit{denseMachine}, \operatorname{denseOutput}\left(w\right)\right)\right), 80 \cdot \left(\operatorname{length}\left(w\right) + 1\right)^{2}\right)\right) \land \left(\operatorname{length}\left(\operatorname{denseOutput}\left(w\right)\right) \le \operatorname{length}\left(w\right)^{2} + 8 \cdot \operatorname{length}\left(w\right) + 7 \land \left(\operatorname{readWord}\left(\mathit{false}, \operatorname{denseOutput}\left(w\right)\right) = \operatorname{some}\left(\operatorname{densePrepared}\left(w\right)\right) \land \left(\left(\forall c \in \mathit{Clause},\; c \in \operatorname{snd}\left(\operatorname{densePrepared}\left(w\right)\right) \Rightarrow \operatorname{length}\left(c\right) \le 3\right) \land \operatorname{unaryCount}\left(\operatorname{snd}\left(\operatorname{densePrepared}\left(w\right)\right)\right) = \operatorname{rawCount}\left(w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DenseClauseConversion.dense_word_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source problem counts assignments to exactly the distinct canonical binary names appearing in the decoded ordinary clauses. A malformed word has count zero. The dictionary retains the rightmost occurrence of each name, and its first-index lookup determines the dense unary variable.

One fixed eighteen-stack Boolean machine runs the whole-word parser, constructs the dictionary with paid comparisons and restoration, writes the explicit dimension and every dense literal index, clears the dictionary and reverses the output. All scratch stacks and finite control reset in the exact haltList configuration. Its direct bound is eighty times (input length plus one) squared. The returned word has length at most the square of input length plus eight times input length plus seven.

The returned source decodes to the total prepared explicit-universe formula and every clause has at most three literals. An assignment equivalence through the actual deduplicated dictionary preserves ordinary CNF evaluation and the number of satisfying assignments. Rejection returns the valid zero-variable one-empty-clause source 0011000. That same word can also arise from a valid empty-clause source; output equality does not characterize rejection. Empty formulas, repeated literals and tautologies are included. No Hamiltonian or oracle occurs in this counting definition.

## References

- Truth anchor: `D5/S0/Computability/DenseClauseConversion.dense_word_run`
- Dependency: [D5/S0/Computability/ClauseWordCodec](ClauseWordCodec.md)
- Dependency: [D5/S0/Computability/DenseClauseExecution](DenseClauseExecution.md)
