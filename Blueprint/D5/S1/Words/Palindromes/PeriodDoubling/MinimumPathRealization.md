# Complete Lowest-Position Product Realization

## Abstract

Every base path lifts to the complete product graph and records exactly its lowest-position escape events.

**Theorem 1.1 (The product flag is the event disjunction).**

$$\forall s \in \operatorname{Fin}\left(1492\right),\; \forall t \in \operatorname{Fin}\left(1492\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; s \in \operatorname{start}\left(\operatorname{baseAutomaton}\left(true\right)\right) \Rightarrow \left(\forall p \in \operatorname{Path}\left(\operatorname{baseAutomaton}\left(true\right), s, t, xs\right),\; \exists u \in \operatorname{Fin}\left(1710\right),\; \exists v \in \operatorname{Fin}\left(1710\right),\; \left(\left(\left(u \in \operatorname{start}\left(minimumAutomaton\right) \land \operatorname{fst}\left(\operatorname{minimumTable}\left(\operatorname{val}\left(u\right)\right)\right) = \operatorname{val}\left(s\right)\right) \land \operatorname{fst}\left(\operatorname{minimumTable}\left(\operatorname{val}\left(v\right)\right)\right) = \operatorname{val}\left(t\right)\right) \land \operatorname{Nonempty}\left(\operatorname{Path}\left(minimumAutomaton, u, v, xs\right)\right)\right) \land \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{minimumTable}\left(\operatorname{val}\left(v\right)\right)\right)\right) = \operatorname{any}\left(id, \operatorname{pathOutputs}\left(\lambda s0:\operatorname{Fin}\left(1492\right) [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] q:\operatorname{Fin}\left(1492\right) \mapsto \operatorname{Bool.and}\left(\operatorname{Bool.and}\left((\operatorname{getD}\left(\operatorname{ite}\left(14 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(s0\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(s0\right)\right)\right), 14\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 0), (\operatorname{getD}\left(\operatorname{ite}\left(10 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(q\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(q\right)\right)\right), 10\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 0)\right), (\operatorname{getD}\left(\operatorname{ite}\left(12 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(q\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(q\right)\right)\right), 12\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0)\right), p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/MinimumPathRealization.minimum_path_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lift preserves each of the four labels and the initial and final base-state indices. It starts with a false flag. Its final flag equals the Boolean disjunction of the path events: no input nonzero has yet been recorded, the current input digit is zero, and the current output digit is nonzero. No accepting-endpoint premise is needed for path construction; if the flag is true and the base endpoint accepts, the lifted path accepts in minimumAutomaton. any is Boolean list disjunction, id is the Boolean identity, and the anonymous bracket in the event lambda represents the unused edge-label argument.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MinimumPathRealization.minimum_path_realization`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseSignedStreams](BaseSignedStreams.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate](MinimumPositionCertificate.md)
