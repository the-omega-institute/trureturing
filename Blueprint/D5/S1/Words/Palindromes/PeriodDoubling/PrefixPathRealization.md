# Complete Representation of Marker Paths

## Abstract

Literal marker transitions are represented completely by the finite product graph.

**Definition 1.1 (The marker transition graph before indexing).**

$$prefixRawAutomaton = \operatorname{NFA.mk}\left(s:\operatorname{List}\left(\mathbb{Z}\right) \mapsto a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \{t:\operatorname{List}\left(\mathbb{Z}\right) \mid (t, a) \in \operatorname{successors}\left(s\right)\}, \operatorname{univ}\left(\operatorname{List}\left(\mathbb{Z}\right)\right), \operatorname{univ}\left(\operatorname{List}\left(\mathbb{Z}\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization.prefixRawAutomaton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

States are lists of integer components and each step is one of the literal marker successors. This transition graph places no conditions on its endpoints: its start and accept sets are universal. A separate condition picks the source and final flags when a cut is realized. The four alphabet coordinates are the signed-weight charge, signed-digit charge and the two shifted input bits.

**Theorem 1.2 (Every marker path stays in the finite graph).**

$$\forall charge \in \operatorname{Bool},\; \forall s \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall t \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \operatorname{Nonempty}\left(\operatorname{Path}\left(prefixRawAutomaton, s, t, xs\right)\right) \Rightarrow \left(\forall u \in \operatorname{Fin}\left(4262\right),\; \operatorname{fst}\left(\operatorname{prefixTable}\left(\operatorname{val}\left(u\right)\right)\right) = s \Rightarrow \left(\exists v \in \operatorname{Fin}\left(4262\right),\; \operatorname{fst}\left(\operatorname{prefixTable}\left(\operatorname{val}\left(v\right)\right)\right) = t \land \operatorname{Nonempty}\left(\operatorname{Path}\left(\operatorname{prefixAutomaton}\left(charge\right), u, v, xs\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization.prefix_path_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting at any represented state, every symbolic marker path lifts to an indexed path with identical edge labels and identical final components. Complete successor reconstruction is checked at all 4262 product rows. Induction on the arbitrary finite path constructs each indexed successor. This proves completeness of the finite carrier; recognizing the literal marked prefix and its tail phases remains a separate arithmetic step.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization.prefixRawAutomaton`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization.prefix_path_realization`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate0](PrefixRealizationCertificate0.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate1](PrefixRealizationCertificate1.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate2](PrefixRealizationCertificate2.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate3](PrefixRealizationCertificate3.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate4](PrefixRealizationCertificate4.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate5](PrefixRealizationCertificate5.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate6](PrefixRealizationCertificate6.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate7](PrefixRealizationCertificate7.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate8](PrefixRealizationCertificate8.md)
