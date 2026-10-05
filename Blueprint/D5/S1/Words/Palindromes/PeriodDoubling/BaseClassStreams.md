# Class Spacing of Transducer Outputs

## Abstract

Both signed streams of any path ending at a valid charge-mode goal forbid opposite digits at distance two.

**Definition 1.1 (Digit memories and persistent class flag).**

$$\forall i \in \mathbb{N},\; \operatorname{classRowCheck}\left(i\right) = \operatorname{all}\left(e:\mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \operatorname{decide}\left(\left(\left(\operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 11\right), 0\right) = \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 10\right), 0\right) \land \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 13\right), 0\right) = \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 12\right), 0\right)\right) \land \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 10\right), 0\right) \cdot \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 11\right), 0\right) \ne \operatorname{neg}\left(1\right)\right) \land \left(\operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 18\right), 0\right) = 0 \Rightarrow \left(\operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 18\right), 0\right) = 0 \land \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 12\right), 0\right) \cdot \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 13\right), 0\right) \ne \operatorname{neg}\left(1\right)\right)\right)\right), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{baseTable}\left(i\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseClassStreams.classRowCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The checker tests both shifted digit memories, immediate rejection of an input violation, and backward propagation of the output violation flag on every base edge.

**Theorem 1.2 (No opposite signs two digit positions apart).**

$$\forall output \in \operatorname{Bool},\; \forall s \in \operatorname{Fin}\left(1492\right),\; \forall t \in \operatorname{Fin}\left(1492\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; t \in \operatorname{accept}\left(\operatorname{baseAutomaton}\left(\operatorname{true}\right)\right) \Rightarrow \left(\forall p \in \operatorname{Path}\left(\operatorname{baseAutomaton}\left(\operatorname{true}\right), s, t, xs\right),\; \operatorname{IsChain}\left(\operatorname{zip}\left(\operatorname{pathOutputs}\left(\operatorname{baseAutomaton}\left(\operatorname{true}\right), \lambda [\operatorname{Fin}\left(1492\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] q:\operatorname{Fin}\left(1492\right) \mapsto \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(q\right)\right)\right), \operatorname{ite}\left(output, 12, 10\right)\right), 0\right), p\right), \operatorname{tail}\left(\operatorname{pathOutputs}\left(\operatorname{baseAutomaton}\left(\operatorname{true}\right), \lambda [\operatorname{Fin}\left(1492\right)] [\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}] q:\operatorname{Fin}\left(1492\right) \mapsto \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(q\right)\right)\right), \operatorname{ite}\left(output, 12, 10\right)\right), 0\right), p\right)\right)\right), a:\mathbb{Z} \times \mathbb{Z} \mapsto b:\mathbb{Z} \times \mathbb{Z} \mapsto \operatorname{fst}\left(a\right) \cdot \operatorname{snd}\left(b\right) \ne \operatorname{neg}\left(1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/BaseClassStreams.base_path_class_spacing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

output selects target component 12 when true and component 10 when false. Zip the digit stream with its tail. Consecutive pairs (a,b) and (b,c) satisfy a times c unequal to minus one. Together with the sparse signed-digit property, this is the class S condition that consecutive nonzero digits of opposite signs have gap at least three. The input transducer rejects violations immediately. The output stores a persistent violation flag, which is zero at every charge-mode accepting goal. Induction propagates that flag backwards and reconstructs each triple from the two digit memories. This result does not assert completeness for actual palindrome cuts.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseClassStreams.base_path_class_spacing`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseClassStreams.classRowCheck`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseSignedStreams](BaseSignedStreams.md)
