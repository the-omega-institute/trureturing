# Unary Clause Query Preparation

## Abstract

A fixed finite transducer preserves raw unary clauses in a succinct query word.

**Theorem 1.1 (Exact query output and quadratic native runtime).**

$$\forall n \in \mathit{Nat},\; \forall F \in \operatorname{UnaryFormula}\left(n\right),\; \left(\forall c \in F,\; \operatorname{length}\left(c\right) \le 3\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{TM2OutputsInTime}\left(\mathit{preMachine}, \operatorname{sourceWord}\left(F\right), \operatorname{some}\left(\operatorname{queryWord}\left(F\right)\right), 3 \cdot \left(\operatorname{length}\left(\operatorname{sourceWord}\left(F\right)\right) + 3\right)^{2} + 7\right)\right) \land \operatorname{length}\left(\operatorname{queryWord}\left(F\right)\right) = \operatorname{length}\left(\operatorname{sourceWord}\left(F\right)\right) + 6 + \operatorname{length}\left(F\right) \cdot \left(n + 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/ClauseQueryPreprocessor.pre_query_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an explicit universe of n variables and raw clauses with at most three literals each, indices are unary and strictly below n. The source word contains the unary universe, clause tags, literal polarities and terminated indices; it is the input to source validation. The physical query is its output. The fixed program has five Boolean stacks, nineteen labels and thirty-six control states.

The exact native run produces the fixed query framing, the universe and one coefficient n plus one for each unchanged raw clause. It clears every input and work stack, resets the finite state, and halts with only the output word. If L is the complete source length, its transitions are bounded by three times (L plus three) squared, plus seven.

The exact output length is L plus six plus the number of clauses times (n plus two). Empty formulas, empty clauses, repeated literals, tautologies and unused variables are all included without changing the physical clauses.

The concrete source 0011000 encodes zero variables and one empty clause. It is accepted and produces the same physical dummy query used by rejection cleanup. The source decoder and execution phase determine acceptance; equality of physical outputs does not.

The proved run is for valid encoded formulas. Total word decoding, malformed-word correctness and the conventional appearing-variable counting correspondence are separate obligations.

## References

- Truth anchor: `D5/S0/Computability/ClauseQueryPreprocessor.pre_query_run`
