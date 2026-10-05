# Marked Suffix Agreement

## Abstract

A good terminal marker flag forces higher input and output coefficients to agree.

**Theorem 1.1 (Agreement above the selected marker).**

$$\forall s \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall t \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \forall p \in \operatorname{Path}\left(\operatorname{prefixRawAutomaton}, s, t, xs\right),\; \left(\left(\operatorname{getD}\left(\operatorname{getElemOption}\left(s, 1\right), 0\right) = 1 \lor \left(\operatorname{getD}\left(\operatorname{getElemOption}\left(s, 1\right), 0\right) = 2 \lor \left(\operatorname{getD}\left(\operatorname{getElemOption}\left(s, 1\right), 0\right) = 3 \lor \operatorname{getD}\left(\operatorname{getElemOption}\left(s, 1\right), 0\right) = 4\right)\right)\right) \land \operatorname{getD}\left(\operatorname{getElemOption}\left(t, 7\right), 0\right) = 0\right) \Rightarrow \left(\left(\operatorname{getD}\left(\operatorname{getElemOption}\left(s, 7\right), 0\right) = 0 \land \operatorname{pathOutputs}\left(\lambda [\operatorname{List}\left(\mathbb{Z}\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] q:\operatorname{List}\left(\mathbb{Z}\right) \mapsto \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{getElemOption}\left(q, 0\right), 0\right)\right)\right)\right), 10\right), 0\right), p\right) = \operatorname{pathOutputs}\left(\lambda [\operatorname{List}\left(\mathbb{Z}\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] q:\operatorname{List}\left(\mathbb{Z}\right) \mapsto \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{getElemOption}\left(q, 0\right), 0\right)\right)\right)\right), 12\right), 0\right), p\right)\right) \land \left(\forall k \in \mathbb{N},\; \left(3 \le k \land k \le 6\right) \Rightarrow \operatorname{getD}\left(\operatorname{getElemOption}\left(t, k\right), 0\right) = \operatorname{getD}\left(\operatorname{getElemOption}\left(s, k\right), 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/MarkedSuffixAgreement.marked_suffix_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The starting marker has already selected its lowest positive digit, so its mode is one, two, three or four. If the final bad flag is zero, every later input coefficient equals its output coefficient and the starting bad flag is zero. Slots three through six, which store the marker parity, retention flag and the two tail phases, keep their starting values throughout the path.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedSuffixAgreement.marked_suffix_agreement`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseSignedStreams](BaseSignedStreams.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization](PrefixPathRealization.md)
