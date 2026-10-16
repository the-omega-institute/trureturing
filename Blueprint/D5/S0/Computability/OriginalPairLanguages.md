# The ordered original guarded pair language

## Abstract

All raw outer words have an exact guarded intersection characterization.

**Theorem 1.1 (UNSAT is first and SAT is second).**

$$\forall w \in \mathit{Word},\; \operatorname{Q}\left(w\right) \Leftrightarrow \left(\left(\neg \operatorname{S}\left(\operatorname{leftGuard}\left(w\right)\right)\right) \land \operatorname{S}\left(\operatorname{rightGuard}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/OriginalPairLanguages.pair_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer decoder projects the first component with a valid true fallback and the second with a valid false fallback. Each component is then repaired with the corresponding original unrestricted guard. Thus the left factor is complement SAT after true repair, and the right factor is SAT after false repair. Their conjunction equals the exact language Q on every raw word. Invalid outer pairs and either invalid component are excluded. Payloads keep the original formulaWord bytes, arbitrary finite clause and name lengths, repetitions, tautologies, and both empty boundaries. This is a semantic decomposition; polynomial execution of the decoder repair requires its source-semantic connection to the lexical machine.

## References

- Truth anchor: `D5/S0/Computability/OriginalPairLanguages.pair_split`
- Dependency: [D5/S0/Computability/BinaryMachine/PairProjection](BinaryMachine/PairProjection.md)
- Dependency: [D5/S0/Computability/OriginalClauseLanguages](OriginalClauseLanguages.md)
