# Dense Parser Instruction Refinement

## Abstract

The translated finite parser restores raw words and identifies complete accepted syntax.

**Theorem 1.1 (Dense Parser Instruction Refinement).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{denseMachine}\right), \operatorname{initList}\left(\mathit{denseMachine}, w\right), \operatorname{some}\left(\operatorname{Cfg}\left(\operatorname{some}\left(\mathit{parseReturn}\right), \mathit{denseLocal}, \operatorname{denseParserStacks}\left(\operatorname{parseStacks}\left(w, \mathit{nil}, \operatorname{decodedOccurrences}\left(w\right), \operatorname{singleton}\left(\operatorname{isSome}\left(\operatorname{readWord}\left(w\right)\right)\right), \mathit{nil}\right)\right)\right)\right), 4 \cdot \operatorname{length}\left(w\right) + 5\right)\right) \land \left(\forall F \in \mathit{ConventionalFormula},\; \operatorname{readWord}\left(w\right) = \operatorname{some}\left(F\right) \Rightarrow \left(w = \operatorname{formulaWord}\left(F\right) \land \left(\forall c \in \mathit{Clause},\; c \in F \Rightarrow \operatorname{length}\left(c\right) \le 3\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DenseClauseMachine.dense_parser_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every raw Boolean word, instruction translation executes the actual parser to the parseReturn boundary within four times input length plus five steps. The input is restored, saved stacks are empty, and the decoder determines the occurrence stream and result flag. A grammar induction on that same word shows that every accepted formula reproduces the complete original spelling and has clauses of width at most three. The endpoint is a parser phase boundary, before dictionary construction and dense output.

## References

- Truth anchor: `D5/S0/Computability/DenseClauseMachine.dense_parser_run`
- Dependency: [D5/S0/Computability/BinaryNameDeduplication](BinaryNameDeduplication.md)
- Dependency: [D5/S0/Computability/ClauseWordCodec](ClauseWordCodec.md)
