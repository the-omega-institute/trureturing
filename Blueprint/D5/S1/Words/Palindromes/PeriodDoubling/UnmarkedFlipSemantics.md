# Unmarked Flip Semantics

## Abstract

The unmarked flip flag records pointwise negation of the lower signed streams.

**Theorem 1.1 (Exact meaning of the persistent flip flag).**

$$\forall s \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall t \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \forall p \in \operatorname{Path}\left(\operatorname{prefixRawAutomaton}, s, t, xs\right),\; \operatorname{getD}\left(\operatorname{getElemOption}\left(t, 1\right), 0\right) = 0 \Rightarrow \left(\operatorname{getD}\left(\operatorname{getElemOption}\left(t, 2\right), 0\right) \ne 0 \Leftrightarrow \left(\operatorname{getD}\left(\operatorname{getElemOption}\left(s, 2\right), 0\right) \ne 0 \land \left(\forall z \in \mathbb{Z} \times \mathbb{Z},\; z \in \operatorname{zip}\left(\operatorname{pathOutputs}\left(\lambda [\operatorname{List}\left(\mathbb{Z}\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] q:\operatorname{List}\left(\mathbb{Z}\right) \mapsto \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{getElemOption}\left(q, 0\right), 0\right)\right)\right)\right), 10\right), 0\right), p\right), \operatorname{pathOutputs}\left(\lambda [\operatorname{List}\left(\mathbb{Z}\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] q:\operatorname{List}\left(\mathbb{Z}\right) \mapsto \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{getElemOption}\left(q, 0\right), 0\right)\right)\right)\right), 12\right), 0\right), p\right)\right) \Rightarrow \operatorname{fst}\left(z\right) + \operatorname{snd}\left(z\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/UnmarkedFlipSemantics.unmarked_path_flip_semantics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A path ending in marker mode zero has remained unmarked throughout. Its final flip flag is nonzero exactly when the starting flag is nonzero and every emitted input/output coefficient pair sums to zero. The two streams have the same length because each transition emits one coefficient on each side. Starting with flip flag one therefore records exact negation of the whole lower signed tail.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/UnmarkedFlipSemantics.unmarked_path_flip_semantics`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseSignedStreams](BaseSignedStreams.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization](PrefixPathRealization.md)
