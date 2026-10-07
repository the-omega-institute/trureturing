# Literal Most Recent Sign Memory

## Abstract

The most recent sign memory equals the last nonzero emitted coefficient.

**Theorem 1.1 (The literal minimum-position transition law).**

$$\forall charge \in \operatorname{Bool},\; \forall output \in \operatorname{Bool},\; \forall s \in \operatorname{Fin}\left(1492\right),\; \forall t \in \operatorname{Fin}\left(1492\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; s \in \operatorname{start}\left(\operatorname{baseAutomaton}\left(charge\right)\right) \Rightarrow \left(\forall p \in \operatorname{Path}\left(\operatorname{baseAutomaton}\left(charge\right), s, t, xs\right),\; \operatorname{getD}\left(\operatorname{ite}\left(\operatorname{ite}\left(output, 17, 16\right) < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(t\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(t\right)\right)\right), \operatorname{ite}\left(output, 17, 16\right)\right)\right), \operatorname{none}\left(\right)\right), 0\right) = \operatorname{getD}\left(\operatorname{ite}\left(\operatorname{filter}\left(z:\mathbb{Z} \mapsto (z != 0), \operatorname{pathOutputs}\left(\lambda [\operatorname{Fin}\left(1492\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] q:\operatorname{Fin}\left(1492\right) \mapsto \operatorname{getD}\left(\operatorname{ite}\left(\operatorname{ite}\left(output, 12, 10\right) < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(q\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(q\right)\right)\right), \operatorname{ite}\left(output, 12, 10\right)\right)\right), \operatorname{none}\left(\right)\right), 0\right), p\right)\right) = [], \operatorname{none}, \operatorname{some}\left(\operatorname{List.getLast}\left(\operatorname{filter}\left(z:\mathbb{Z} \mapsto (z != 0), \operatorname{pathOutputs}\left(\lambda [\operatorname{Fin}\left(1492\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] q:\operatorname{Fin}\left(1492\right) \mapsto \operatorname{getD}\left(\operatorname{ite}\left(\operatorname{ite}\left(output, 12, 10\right) < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(q\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(q\right)\right)\right), \operatorname{ite}\left(output, 12, 10\right)\right)\right), \operatorname{none}\left(\right)\right), 0\right), p\right)\right)\right)\right)\right), 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/BaseLastSignMemory.base_path_last_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either emitted stream, each literal base edge updates the most recent sign when its new coefficient is nonzero. Induction along an arbitrary source path identifies the terminal memory with the last nonzero coefficient of the emitted stream. All source memories start at zero, and absent last entries use default zero. Acceptance and tightness are unnecessary; this statement also applies to the partial path before a marker is selected. The last-option expression is none for an empty list and some(List.getLast(...)) otherwise; the nonempty proof argument is implicit.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseLastSignMemory.base_path_last_sign`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseChargeArithmetic](BaseChargeArithmetic.md)
