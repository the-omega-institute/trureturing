# Marked Input Shape

## Abstract

The marker modes recognize positive signed digits at positions separated by three.

**Theorem 1.1 (Input language of a completed marker).**

$$\forall s \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall t \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \forall p \in \operatorname{Path}\left(\operatorname{prefixRawAutomaton}, s, t, xs\right),\; \left(\operatorname{getD}\left(\operatorname{ite}\left(1 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 1\right)\right), \operatorname{none}\left(\right)\right), 0\right) = 0 \land \operatorname{getD}\left(\operatorname{ite}\left(1 < \operatorname{List.length}\left(t\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(t, 1\right)\right), \operatorname{none}\left(\right)\right), 0\right) = 4\right) \Rightarrow \left(\exists lower \in \operatorname{List}\left(\mathbb{Z}\right),\; \exists m \in \mathbb{N},\; \exists k \in \mathbb{N},\; 0 < m \land \operatorname{pathOutputs}\left(\lambda [\operatorname{List}\left(\mathbb{Z}\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] q:\operatorname{List}\left(\mathbb{Z}\right) \mapsto \operatorname{getD}\left(\operatorname{ite}\left(10 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(q\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(q, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(q\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(q, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)\right)\right), 10\right)\right), \operatorname{none}\left(\right)\right), 0\right), p\right) = \operatorname{append}\left(\operatorname{append}\left(lower, \operatorname{flatten}\left(\operatorname{replicate}\left(m, [1, 0, 0]\right)\right)\right), \operatorname{replicate}\left(k + 1, 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/PrefixInputShape.prefix_path_input_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A path begins in marker mode zero and ends in mode four. Its input coefficients consist of an arbitrary lower tail, a nonempty repetition of the block [1,0,0], and at least one final zero. Coefficients are read least significant first. Modes one and two require the two zeros after a selected positive digit; mode three either starts the next block or ends the marker; mode four accepts only zeros.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/PrefixInputShape.prefix_path_input_shape`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseSignedStreams](BaseSignedStreams.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization](PrefixPathRealization.md)
