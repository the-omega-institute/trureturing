# Binary Name Dictionary Lookup

## Abstract

Whole-name lookup restores the serialized dictionary and reports its dense position.

**Theorem 1.1 (Actual finite execution, exact restored words and paid scan clock).**

$$\forall query \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall names \in \operatorname{List}\left(\operatorname{List}\left(\mathit{Bool}\right)\right),\; \forall frame \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{dictionaryMachine}\right), \operatorname{lookupCfg}\left(\mathit{start}, \mathit{query}, \mathit{nil}, \mathit{nil}, \mathit{nil}, \mathit{frame}, \operatorname{dictionaryStream}\left(\mathit{names}\right), \mathit{nil}, \mathit{nil}, \mathit{false}\right), \operatorname{some}\left(\operatorname{dictionaryCfg}\left(\mathit{none}, ((\mathit{none}, \mathit{none}, \mathit{true}), \mathit{none}, \mathit{false}), \operatorname{compareStacks}\left(\mathit{query}, \mathit{nil}, \mathit{nil}, \mathit{nil}, \mathit{nil}, \mathit{frame}\right), \operatorname{dictionaryStream}\left(\mathit{names}\right), \mathit{nil}, \operatorname{cons}\left(\operatorname{decide}\left(\mathit{query} \in \mathit{names}\right), \operatorname{replicate}\left(\operatorname{idxOf}\left(\mathit{query}, \mathit{names}\right), \mathit{true}\right)\right)\right)\right), \left(2 \cdot \operatorname{length}\left(\mathit{query}\right) + 12\right) \cdot \operatorname{length}\left(\mathit{names}\right) + 4 \cdot \operatorname{length}\left(\operatorname{dictionaryStream}\left(\mathit{names}\right)\right) + 3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryNameDictionary.dictionary_lookup_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary query name, list of dictionary names and caller frame, the nine-stack machine scans the private serialized dictionary. Each entry stores its reversed binary spelling in escaped pairs. Real pushes extract the candidate, the included comparison program backs up and restores both operands, and cleanup drains the candidate stack.

The final index stack contains the membership flag followed by the unary first-occurrence index; absence uses the dictionary length sentinel. The query and entire dictionary stream are restored literally, all backups and comparison output are empty, and the caller frame is preserved. The bound is (2 times query length plus 12) times the number of names, plus four times serialized dictionary length, plus three.

This is a routine boundary for arbitrary names and dictionary order. The theorem does not supply the preceding raw-source parser, rightmost deduplication or count-preserving complete converter. Those stages must establish the actual dictionary used by this scan.

## References

- Truth anchor: `D5/S0/Computability/BinaryNameDictionary.dictionary_lookup_run`
- Dependency: [D5/S0/Computability/BinaryNameComparison](BinaryNameComparison.md)
- Dependency: [D5/S0/Computability/ConventionalClauseWords](ConventionalClauseWords.md)
