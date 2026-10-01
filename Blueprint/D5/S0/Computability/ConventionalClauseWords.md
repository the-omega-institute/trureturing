# Conventional Appearing Name Clause Words

## Abstract

Conventional clause parsing has an actual finite scan and exact restored source.

**Theorem 1.1 (Whole-word parser execution and paid occurrence materialization).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall frame \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{parseMachine}\right), \operatorname{parseCfg}\left(\operatorname{some}\left(\mathit{scan}\right), \mathit{bodyFirst}, 0, w, \mathit{nil}, \mathit{nil}, \mathit{nil}, \mathit{frame}, \mathit{false}\right), \operatorname{some}\left(\operatorname{parseCfg}\left(\mathit{none}, \mathit{bodyFirst}, 0, w, \mathit{nil}, \operatorname{decodedOccurrences}\left(w\right), \operatorname{singleton}\left(\operatorname{isSome}\left(\operatorname{readWord}\left(w\right)\right)\right), \mathit{frame}, \mathit{false}\right)\right), 4 \cdot \operatorname{length}\left(w\right) + 5\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/ConventionalClauseWords.conventional_word_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Names are positive most significant bit first binary spellings, escaped as one followed by each bit and terminated by zero. Each clause has at most three signed literals. The formula ends in exactly two zeros. There is no explicit variable-universe header: assignments in the independent raw count range over exactly the distinct names appearing in the decoded clauses.

For every raw Boolean word and caller frame, the five-stack finite parser scans the actual input, saves each consumed symbol, writes escaped name occurrences, and restores the original word literally. Accepted words return the decoder's reversed occurrence stream and the flag true. Rejected words return an empty occurrence stack and the flag false. Missing or noncanonical names, fourth literals, truncation and trailing symbols take the actual cleanup branch. The saved stack is empty, the control is reset and the arbitrary caller frame is preserved.

The bound is four times raw input length plus five. The statement is a parser routine boundary with restored source and occurrence output; dense relabeling, assignment transport and the complete physical protocol require the further word conversion stages.

## References

- Truth anchor: `D5/S0/Computability/ConventionalClauseWords.conventional_word_run`
