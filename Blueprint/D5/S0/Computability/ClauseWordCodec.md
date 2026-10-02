# Raw Clause Word Codec

## Abstract

Total decoding determines every raw clause and the exact physical query framing.

**Theorem 1.1 (Soundness, roundtrip and unique complete syntax).**

$$\forall physical \in \mathit{Bool},\; \forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall n \in \mathit{Nat},\; \forall F \in \operatorname{UnaryFormula}\left(n\right),\; \operatorname{readWord}\left(\mathit{physical}, w\right) = \operatorname{some}\left(\langle n,F\rangle\right) \Leftrightarrow \left(w = \operatorname{encodeWord}\left(\mathit{physical}, F\right) \land \left(\forall c \in F,\; \operatorname{length}\left(c\right) \le 3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/ClauseWordCodec.codec_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either source or physical mode, an arbitrary Boolean word decodes to universe n and formula F exactly when it is the complete encoding of those raw clauses and each clause has at most three literals. The parser receives no decoding witness. It checks terminated unary indices against the parsed universe, and the physical mode checks each coefficient equals n plus one.

Source words have the explicit unary universe, clause and literal tags, polarities and final delimiter. Physical words additionally have the fixed query prefix, beta and visible tokens, and one terminated coefficient per raw clause. Every bit is consumed. Empty formulas, empty clauses, zero variables, unused variables, repeated literals and tautologies retain their exact syntax.

The recursive proof establishes soundness of every accepted literal and clause and completeness with fuel derived from the word length. A deterministic decoder makes accepted encodings unique. This result supplies the raw-word codec; the universal malformed finite-machine run, physical oracle relation and conventional counting transducers remain separate counting reduction obligations.

## References

- Truth anchor: `D5/S0/Computability/ClauseWordCodec.codec_exact`
- Dependency: [D5/S0/Computability/ClauseQueryPreprocessor](ClauseQueryPreprocessor.md)
