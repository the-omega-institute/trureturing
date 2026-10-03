# Binary Name Dictionary Construction

## Abstract

Occurrence-driven construction writes the rightmost-deduplicated dictionary.

**Theorem 1.1 (Actual lookup, insertion and a quadratic charged clock).**

$$\forall names \in \operatorname{List}\left(\operatorname{List}\left(\mathit{Bool}\right)\right),\; \forall frame \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall dimension \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{builderMachine}\right), \operatorname{buildCfg}\left(\mathit{start}, \mathit{nil}, \mathit{nil}, \mathit{nil}, \operatorname{dictionaryStream}\left(\operatorname{reverse}\left(\mathit{names}\right)\right), \mathit{dimension}, \mathit{frame}, \mathit{false}\right), \operatorname{some}\left(\operatorname{builderCfg}\left(\mathit{none}, ((\mathit{none}, \mathit{none}, \mathit{true}), \mathit{none}, \mathit{false}), \operatorname{dictionaryStacks}\left(\operatorname{compareStacks}\left(\mathit{nil}, \mathit{nil}, \mathit{nil}, \mathit{nil}, \mathit{nil}, \mathit{frame}\right), \operatorname{dictionaryStream}\left(\operatorname{dedup}\left(\mathit{names}\right)\right), \mathit{nil}, \mathit{nil}\right), \mathit{nil}, \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{length}\left(\operatorname{dedup}\left(\mathit{names}\right)\right), \mathit{true}\right), \mathit{dimension}\right)\right)\right), 20 \cdot \operatorname{pow}\left(\operatorname{length}\left(\operatorname{dictionaryStream}\left(\mathit{names}\right)\right) + 1, 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryNameDeduplication.dictionary_build_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every list of binary names, the eleven-stack machine scans its serialized occurrences in reverse order. It extracts each whole name with real pops and invokes the included finite dictionary-lookup program. The resulting membership flag selects an actual discard or insertion branch.

Every unseen name is written to the head of the dictionary in escaped reversed spelling; the dimension stack receives one true symbol. The final dictionary equals the pinned rightmost-occurrence deduplication of the original list. All comparison backups, candidates, history, index and occurrence stacks are empty at return. The arbitrary caller frame and dimension suffix are preserved.

The clock is at most twenty times (serialized occurrence length plus one) squared. It charges extraction, comparison, operand and dictionary restoration, index draining and insertion. This routine does not yet parse arbitrary conventional clause words or relabel their literals.

## References

- Truth anchor: `D5/S0/Computability/BinaryNameDeduplication.dictionary_build_run`
- Dependency: [D5/S0/Computability/BinaryNameDictionary](BinaryNameDictionary.md)
