# Base Projection of Marked Paths

## Abstract

Base Projection of Marked Paths.

**Theorem 1.1 (Path projection and digit equality).**

$$\forall charge \in \operatorname{Bool},\; \forall s \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall t \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \forall p \in \operatorname{Path}\left(prefixRawAutomaton, s, t, xs\right),\; \forall u \in \operatorname{Fin}\left(1492\right),\; \operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right) = \operatorname{cast}\left(\operatorname{val}\left(u\right), \mathbb{Z}\right) \Rightarrow \left(\exists v \in \operatorname{Fin}\left(1492\right),\; \exists q \in \operatorname{Path}\left(\operatorname{baseAutomaton}\left(charge\right), u, v, xs\right),\; \operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(t\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(t, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right) = \operatorname{cast}\left(\operatorname{val}\left(v\right), \mathbb{Z}\right) \land \left(\forall output \in \operatorname{Bool},\; \operatorname{pathOutputs}\left(\lambda [\operatorname{List}\left(\mathbb{Z}\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] r:\operatorname{List}\left(\mathbb{Z}\right) \mapsto \operatorname{getD}\left(\operatorname{ite}\left(\operatorname{ite}\left(output, 12, 10\right) < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(r\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(r, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(r\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(r, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)\right)\right), \operatorname{ite}\left(output, 12, 10\right)\right)\right), \operatorname{none}\left(\right)\right), 0\right), p\right) = \operatorname{pathOutputs}\left(\lambda [\operatorname{Fin}\left(1492\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] r:\operatorname{Fin}\left(1492\right) \mapsto \operatorname{getD}\left(\operatorname{ite}\left(\operatorname{ite}\left(output, 12, 10\right) < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(r\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(r\right)\right)\right), \operatorname{ite}\left(output, 12, 10\right)\right)\right), \operatorname{none}\left(\right)\right), 0\right), q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/MarkedBaseProjection.marker_base_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The underlying base index follows every raw marker transition. Starting from any valid base index, path induction constructs an indexed base path with the same labels. Its terminal index is exact, and its input and output signed-digit streams equal those observed through the raw marker states. toNat denotes integer conversion to a natural number, and getD uses zero for absent entries.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedBaseProjection.marker_base_projection`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseSignedStreams](BaseSignedStreams.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization](PrefixPathRealization.md)
