# Lowest Signed-Digit Position Certificate

## Abstract

No accepted escape path in the complete lifted graph has positive f weight.

**Definition 1.1 (The complete lifted lowest-position graph).**

$$\forall i \in \mathbb{N},\; \operatorname{minimumTable}\left(i\right):\mathbb{N} \times \operatorname{Bool} \times \operatorname{List}\left(\mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right) \times \operatorname{Option}\left(\mathbb{Z}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.minimumTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For indices zero through 1709, minimumTable selects one of 1710 literal rows through a balanced tree of index comparisons and 64 private minimumTableChunk functions taking the original natural index. Each row lists the base-state index, the persistent lowest-position escape flag, every lifted edge, and the optional integer potential. Base states are the 1492 states of baseTable. Outside this range lookup returns the final row; all runs use Fin 1710.

**Definition 1.2 (The literal lowest-position flag update).**

$$\forall i \in \mathbb{N},\; \operatorname{successors}\left(i\right) = \operatorname{map}\left(\lambda e:\mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto (\operatorname{fst}\left(e\right), \operatorname{Bool.or}\left(\operatorname{fst}\left(\operatorname{snd}\left(\operatorname{minimumTable}\left(i\right)\right)\right), \operatorname{Bool.and}\left(\operatorname{Bool.and}\left((\operatorname{getD}\left(\operatorname{ite}\left(14 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(\operatorname{minimumTable}\left(i\right)\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(\operatorname{minimumTable}\left(i\right)\right)\right)\right), 14\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 0), (\operatorname{getD}\left(\operatorname{ite}\left(10 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 10\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 0)\right), (\operatorname{getD}\left(\operatorname{ite}\left(12 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 12\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0)\right)\right), \operatorname{snd}\left(e\right)), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(\operatorname{minimumTable}\left(i\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.successors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every outgoing base edge, preserve its four labels and attach the persistent flag. The flag is set when the first-input-sign memory is still zero, the newly emitted input digit is zero, and the newly emitted output digit is nonzero. This is the arithmetic update used both by the potential checker and by complete path realization.

**Definition 1.3 (The lowest-position escape automaton).**

$$\operatorname{minimumAutomaton}\left(\right) = \operatorname{NFA.mk}\left(i:\operatorname{Fin}\left(1710\right) \mapsto a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \{j:\operatorname{Fin}\left(1710\right) \mid (\operatorname{val}\left(j\right), a) \in \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{snd}\left(\operatorname{minimumTable}\left(\operatorname{val}\left(i\right)\right)\right)\right)\right)\}, \{i:\operatorname{Fin}\left(1710\right) \mid \operatorname{val}\left(i\right) < 7\}, \{i:\operatorname{Fin}\left(1710\right) \mid \operatorname{Bool.and}\left(\operatorname{Bool.and}\left(\operatorname{fst}\left(\operatorname{snd}\left(\operatorname{minimumTable}\left(\operatorname{val}\left(i\right)\right)\right)\right), \operatorname{baseTerminal}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(\operatorname{minimumTable}\left(\operatorname{val}\left(i\right)\right)\right)\right)\right)\right)\right), (\operatorname{getD}\left(\operatorname{ite}\left(18 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(\operatorname{minimumTable}\left(\operatorname{val}\left(i\right)\right)\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(\operatorname{minimumTable}\left(\operatorname{val}\left(i\right)\right)\right)\right)\right), 18\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 0)\right)\}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.minimumAutomaton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Its seven source indices are zero through six. Edges are literal table entries. A terminal state has the escape flag true and its base state is accepted in the valid-output mode of baseAutomaton. The flag becomes true when an output nonzero digit appears before the first input nonzero digit.

**Theorem 1.4 (The lowest-position escape bound).**

$$\forall s \in \operatorname{Fin}\left(1710\right),\; \forall t \in \operatorname{Fin}\left(1710\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \left(s \in \operatorname{start}\left(\operatorname{minimumAutomaton}\left(\right)\right) \land t \in \operatorname{accept}\left(\operatorname{minimumAutomaton}\left(\right)\right)\right) \Rightarrow \left(\forall p \in \operatorname{Path}\left(\operatorname{minimumAutomaton}\left(\right), s, t, xs\right),\; \operatorname{pathCharge}\left(\lambda [\operatorname{Fin}\left(1710\right)] a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} [\operatorname{Fin}\left(1710\right)] \mapsto \operatorname{fst}\left(a\right), p\right) \le 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.minimum_accepted_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel reduction checks all 1710 rows, verifies complete lifting of the base graph, and proves the source, goal and reverse-closed potential inequalities. Every accepting run has total f charge at most zero. This graph statement requires an arithmetic identification of f with the signed-weight difference before it can imply a statement about actual cuts.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.minimumAutomaton`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.minimumTable`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.minimum_accepted_bound`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.successors`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates](BaseCertificates.md)
