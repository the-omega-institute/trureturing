# Total Clause Machine Word Refinement

## Abstract

The total raw-word parser agrees with the fixed machine's exact clean physical-query output.

**Theorem 1.1 (Arbitrary source words, exact query, and rejection entry).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{TM2OutputsInTime}\left(\mathit{preMachine}, w, \operatorname{some}\left(\operatorname{preparedQuery}\left(w\right)\right), \left(4 \cdot \operatorname{length}\left(w\right) + 20\right) \cdot \operatorname{length}\left(w\right) + 13\right)\right) \land \left(\operatorname{readWord}\left(\mathit{true}, \operatorname{preparedQuery}\left(w\right)\right) = \operatorname{some}\left(\operatorname{preparedFormula}\left(w\right)\right) \land \left(\operatorname{preparedQuery}\left(w\right) = \operatorname{encodeWord}\left(\mathit{true}, \operatorname{snd}\left(\operatorname{preparedFormula}\left(w\right)\right)\right) \land \left(\left(\forall c \in \operatorname{snd}\left(\operatorname{preparedFormula}\left(w\right)\right),\; \operatorname{length}\left(c\right) \le 3\right) \land \left(\operatorname{length}\left(\operatorname{preparedQuery}\left(w\right)\right) \le \left(\left(4 \cdot \operatorname{length}\left(w\right) + 20\right) \cdot \operatorname{length}\left(w\right) + 13\right) \cdot \operatorname{programPushBound}\left(\operatorname{m}\left(\mathit{preMachine}\right)\right) \land \left(\operatorname{readWord}\left(\mathit{false}, w\right) = \mathit{none} \Rightarrow \left(\exists st \in \mathit{PreControl},\; \exists input \in \operatorname{List}\left(\mathit{Bool}\right),\; \exists header \in \operatorname{List}\left(\mathit{Bool}\right),\; \exists scratch \in \operatorname{List}\left(\mathit{Bool}\right),\; \exists query \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{preMachine}\right), \operatorname{initList}\left(\mathit{preMachine}, w\right), \operatorname{some}\left(\operatorname{preCfg}\left(\mathit{badInput}, \mathit{st}, \mathit{input}, \mathit{header}, \mathit{scratch}, \mathit{query}, \mathit{nil}\right)\right), \left(4 \cdot \operatorname{length}\left(w\right) + 20\right) \cdot \operatorname{length}\left(w\right) + 13\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/ClausePreprocessorRefinement.pre_word_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean word w, preparedFormula is its total source decoder result, defaulting to zero variables and one empty clause when decoding fails. preparedQuery is queryWord of the decoded raw formula, or the fixed dummyQuery on failure.

The fixed five-stack machine reaches exactly the clean haltList with preparedQuery within (4L plus 20)L plus 13 actual steps, where L is the input length. The output decodes in physical mode to preparedFormula, equals its complete physical encoding, and has only clauses of width at most three. Its length is at most that step bound times the fixed program push bound.

If the source decoder rejects, the actual run first reaches badInput with empty output and concrete input, header, scratch and query stacks within the same bound. Cleanup then produces the fixed zero-variable, one-empty-clause descriptor. The valid source for that same formula also produces dummyQuery; rejection is determined by the parser and phase, not output equality.

Phase-specific grammar predicates preserve acceptance through actual parsing, copying and restoration steps. Induction along a rejected terminating trace finds its badInput prefix. Accepted words use decoder soundness and the valid-source run. Deterministic terminal uniqueness identifies each output with the already bounded total run. Physical trace values, conventional counting-name conversion, oracle response materialization and the one-call protocol require additional results.

## References

- Truth anchor: `D5/S0/Computability/ClausePreprocessorRefinement.pre_word_run`
- Dependency: [D5/S0/Computability/ClauseMalformedCleanup](ClauseMalformedCleanup.md)
- Dependency: [D5/S0/Computability/ClausePreprocessorClock](ClausePreprocessorClock.md)
- Dependency: [D5/S0/Computability/ClauseWordCodec](ClauseWordCodec.md)
