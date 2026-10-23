# Exact original guarded clause languages

## Abstract

Exact original guarded clause languages.

W is the domain of the unrestricted original decoder. S requires that same decoder and a satisfying assignment on the original appearing-name subtype; U is W and not S. Q is the ordered pair of U first and S second under the unchanged outer pairWords encoding. Empty conjunction and one empty clause give the valid true word 00 and valid false word 011000. False repair always returns a valid original formula and preserves SAT. True repair converts guarded UNSAT exactly to complement SAT; malformed words lie in neither guarded language. The pair equivalence covers all raw outer words.

**Theorem 1.1 (repair_laws).**

$$\forall w \in \mathit{Word},\; \operatorname{W}\left(\operatorname{repair}\left(\mathit{falseWord}, w\right)\right) \land \left(\left(\operatorname{S}\left(\operatorname{repair}\left(\mathit{falseWord}, w\right)\right) \Leftrightarrow \operatorname{S}\left(w\right)\right) \land \left(\left(\operatorname{U}\left(w\right) \Leftrightarrow \left(\neg \operatorname{S}\left(\operatorname{repair}\left(\mathit{trueWord}, w\right)\right)\right)\right) \land \left(\operatorname{W}\left(w\right) \Rightarrow \left(\operatorname{repair}\left(\mathit{falseWord}, w\right) = w \land \operatorname{repair}\left(\mathit{trueWord}, w\right) = w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/OriginalClauseLanguages.repair_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

W is the domain of the unrestricted original decoder. S requires that same decoder and a satisfying assignment on the original appearing-name subtype; U is W and not S. Q is the ordered pair of U first and S second under the unchanged outer pairWords encoding. Empty conjunction and one empty clause give the valid true word 00 and valid false word 011000. False repair always returns a valid original formula and preserves SAT. True repair converts guarded UNSAT exactly to complement SAT; malformed words lie in neither guarded language. The pair equivalence covers all raw outer words.

**Theorem 1.2 (pair_language).**

$$\forall w \in \mathit{Word},\; \operatorname{Q}\left(w\right) \Leftrightarrow \left(\exists u \in \mathit{Word},\; \exists v \in \mathit{Word},\; \operatorname{decodePair}\left(w\right) = \operatorname{some}\left(\operatorname{pair}\left(u, v\right)\right) \land \left(\operatorname{U}\left(u\right) \land \operatorname{S}\left(v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/OriginalClauseLanguages.pair_language` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

W is the domain of the unrestricted original decoder. S requires that same decoder and a satisfying assignment on the original appearing-name subtype; U is W and not S. Q is the ordered pair of U first and S second under the unchanged outer pairWords encoding. Empty conjunction and one empty clause give the valid true word 00 and valid false word 011000. False repair always returns a valid original formula and preserves SAT. True repair converts guarded UNSAT exactly to complement SAT; malformed words lie in neither guarded language. The pair equivalence covers all raw outer words.

## References

- Truth anchor: `D5/S0/Computability/OriginalClauseLanguages.pair_language`
- Truth anchor: `D5/S0/Computability/OriginalClauseLanguages.repair_laws`
- Dependency: [D5/S0/Computability/BinaryMachine/StackPair](BinaryMachine/StackPair.md)
- Dependency: [D5/S0/Computability/UnrestrictedClauseWords](UnrestrictedClauseWords.md)
