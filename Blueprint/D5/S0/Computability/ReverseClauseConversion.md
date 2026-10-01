# Paid Reverse Clause Word Conversion

## Abstract

A fixed finite word transducer preserves explicitly declared variables through ordinary appearing-name clauses.

**Theorem 1.1 (Total word execution, canonical names and complete assignment count).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{reverseMachine}\right), \operatorname{initList}\left(\mathit{reverseMachine}, w\right), \operatorname{some}\left(\operatorname{haltList}\left(\mathit{reverseMachine}, \operatorname{convertedWord}\left(w\right)\right)\right), 10 \cdot \operatorname{length}\left(w\right)^{2} + 41 \cdot \operatorname{length}\left(w\right) + 33\right)\right) \land \left(\operatorname{length}\left(\operatorname{convertedWord}\left(w\right)\right) \le 4 \cdot \operatorname{length}\left(w\right)^{2} + 14 \cdot \operatorname{length}\left(w\right) + 6 \land \left(\operatorname{readWord}\left(\operatorname{convertedWord}\left(w\right)\right) = \operatorname{some}\left(\operatorname{saturatedFormula}\left(\operatorname{snd}\left(\operatorname{preparedFormula}\left(w\right)\right)\right)\right) \land \operatorname{rawCount}\left(\operatorname{convertedWord}\left(w\right)\right) = \operatorname{explicitRawCount}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/ReverseClauseConversion.reverse_word_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every raw unary source runs on the fixed ten-stack Boolean program. The actual preprocessor is translated instruction by instruction; subsequent phases scan coefficients, restore counters, write canonical binary names, append tautologies, reverse the output and empty all scratch stacks. The clock is ten times input length squared plus forty-one times input length plus thirty-three.

The conventional output has length at most four times input length squared plus fourteen times input length plus six. Its whole-word decoder returns precisely the renamed clauses and one tautology for each explicitly declared variable. Assignment equivalence preserves the ordinary CNF count, including unused variables. Tautologies occur only in this consumer encoding and leave the original physical clause family unchanged.

The source decoder determines acceptance. Malformed words produce the conventional zero-variable empty-clause word011000 and count zero; valid source0011000 reaches that same output. Empty formulas, empty clauses, zero variables, repeated literals, and opposite polarities remain in scope. Count is defined from ordinary CNF evaluation independently of any physical trace or oracle.

## References

- Truth anchor: `D5/S0/Computability/ReverseClauseConversion.reverse_word_run`
- Dependency: [D5/S0/Computability/DenseClauseConversion](DenseClauseConversion.md)
- Dependency: [D5/S0/Computability/ReverseClauseMachine](ReverseClauseMachine.md)
