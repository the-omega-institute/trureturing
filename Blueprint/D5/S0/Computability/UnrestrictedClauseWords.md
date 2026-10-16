# Unrestricted Original Clause Words

## Abstract

The original binary-name CNF encoding has an unrestricted total decoder and a fixed finite parser with a linear transition bound.

A formula is an ordered list of clauses over the original Boolean-name literals. A canonical name is a nonempty most significant bit first binary spelling beginning in one. Its bits are escaped as one-bit pairs and terminated by zero. Literal tags, polarity, clause delimiters, and the final two zeros are exactly those of Conventional.formulaWord. There is no variable-universe header and no numerical bound on a name.

**Theorem 1.1 (Exact unrestricted decoding and malformed rejection).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall F \in \mathit{Formula},\; \operatorname{readWord}\left(w\right) = \operatorname{some}\left(F\right) \Leftrightarrow \left(\operatorname{Canonical}\left(F\right) \land w = \operatorname{formulaWord}\left(F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/UnrestrictedClauseWords.word_codec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every raw word and formula, decoding returns that formula exactly when all its names are canonical and the raw word is its original encoding. This gives both the encoded roundtrip and rejection of every word outside the canonical encoded range.

Clause widths are arbitrary finite lengths. The cursor appends the original signed literals in order, preserving repeated clauses, repeated names, and tautologies. The empty conjunction and empty clauses retain their original encodings and semantics. The decoder never constructs a replacement variable dictionary.

The proof reconstructs the exact consumed prefix at every live cursor transition and preserves canonical names. Induction on name bits, literals, and clauses proves that each original encoding reaches its corresponding completed cursor.

**Theorem 1.2 (Actual finite parsing in linear charged time).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{TM2OutputsInTime}\left(\mathit{parser}, w, \operatorname{some}\left(\operatorname{resultWord}\left(\operatorname{readWord}\left(w\right)\right)\right), 2 \cdot \operatorname{length}\left(w\right) + 3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/UnrestrictedClauseWords.parser_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parser is a fixed FinTM2 with Boolean stack alphabets and finite labels and control. Erasing the mathematical cursor's unbounded buffers leaves exactly its lexical control. No clause width counter is installed. Each input bit is read and saved by one actual transition; the machine then copies an accepted word or clears a rejected word before writing its result flag.

For every raw word of length L, execution reaches the standard halt configuration in at most two times L plus three transitions. Rejection returns the singleton false. Success returns true followed by the unchanged original encoding of the decoded formula. All scratch stacks are empty and finite control is reset. Missing names, noncanonical leading bits, malformed delimiters, truncation, and trailing symbols all reject.

This theorem supplies syntax validation and a typed encoded result. Construction and execution of a literal evaluation graph require separate mathematical statements.

## References

- Truth anchor: `D5/S0/Computability/UnrestrictedClauseWords.parser_run`
- Truth anchor: `D5/S0/Computability/UnrestrictedClauseWords.word_codec`
- Dependency: [D5/S0/Computability/ConventionalClauseWords](ConventionalClauseWords.md)
