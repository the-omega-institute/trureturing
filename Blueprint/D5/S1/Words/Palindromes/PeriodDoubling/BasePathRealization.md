# Complete Representation of Arithmetic Transducer Paths

## Abstract

Literal arithmetic paths are represented completely by the finite transducer graph.

**Definition 1.1 (The arithmetic automaton before indexing).**

$$baseRawAutomaton = \operatorname{NFA.mk}\left(s:\operatorname{List}\left(\mathbb{Z}\right) \mapsto a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \{t:\operatorname{List}\left(\mathbb{Z}\right) \mid (t, a) \in \operatorname{baseSuccessors}\left(s\right)\}, \{s:\operatorname{List}\left(\mathbb{Z}\right) \mid s \in initialStates\}, \{t:\operatorname{List}\left(\mathbb{Z}\right) \mid \operatorname{baseTerminal}\left(t\right) = true\}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BasePathRealization.baseRawAutomaton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

States are lists of integer components. The source set is initialStates, each step is one of baseSuccessors, and acceptance requires baseTerminal to be true. The four alphabet coordinates are the signed-weight charge, signed-digit charge and the two shifted input bits. This automaton applies the literal arithmetic operations without restricting its state carrier to the finite table.

**Theorem 1.2 (Every arithmetic path is in the finite graph).**

$$\forall s \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall t \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \left(s \in \operatorname{start}\left(baseRawAutomaton\right) \land t \in \operatorname{accept}\left(baseRawAutomaton\right)\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{Path}\left(baseRawAutomaton, s, t, xs\right)\right) \Rightarrow \left(\exists charge \in \operatorname{Bool},\; \exists i \in \operatorname{Fin}\left(1492\right),\; \exists k \in \operatorname{Fin}\left(1492\right),\; \left(\left(\left(i \in \operatorname{start}\left(\operatorname{baseAutomaton}\left(charge\right)\right) \land k \in \operatorname{accept}\left(\operatorname{baseAutomaton}\left(charge\right)\right)\right) \land \operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(i\right)\right)\right) = s\right) \land \operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(k\right)\right)\right) = t\right) \land \operatorname{Nonempty}\left(\operatorname{Path}\left(\operatorname{baseAutomaton}\left(charge\right), i, k, xs\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/BasePathRealization.base_path_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every source-to-flushed-state path has an indexed path with the identical edge labels and identical initial and final state components. The output violation flag chooses one of the two acceptance modes. All seven source rows and all possible successors of each of the 1492 rows are checked, so path induction covers arbitrary finite lengths. This assertion lifts arithmetic paths; deriving an arithmetic path from a palindrome cut is a separate condition.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BasePathRealization.baseRawAutomaton`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BasePathRealization.base_path_realization`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates](BaseCertificates.md)
