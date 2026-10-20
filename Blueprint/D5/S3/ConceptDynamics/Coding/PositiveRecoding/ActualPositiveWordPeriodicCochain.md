# Actual-history charts, endpoint-corrected positive-word gyration and signed time translation

## Abstract

Actual-history charts, endpoint-corrected positive-word gyration and signed time translation.

These source-bound statements use the forward shift on original signed histories. The finite chart is a coordinate system for those histories and their primitive orbits, not a replacement native action. All integer times remain quantified in ht. All nonzero natural periods are retained here, and localization later restricts only to periods divisible by three.

A supplied full graph chart r writes a time-equivariant history map by composing r.homeomorph inverse, the map, and r.homeomorph. Comparison with the fixed chart is conjugation by chartComparison r. Cancellation of the two full chart equivalences and TimedEquiv.gyration_conjugate gives the same loop value. For composition, cancel the intermediate fixed chart and apply TimedEquiv.gyration_comp. These are local applications of the retained general laws to the same history maps.

**Definition 1.1 (The existing full outgoing chart).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.chart`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.chart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite Presentation F, matrix F is OutSplitNumberedRecoding.R F.graph id multiplied by its S factor. Its rank is the cardinality of the actual vertex type. chart F is exactly outOld F F id, retaining vertex and parallel-edge identities. primitiveChart transports true forward minimal period and orbitChart transports the existing forward-rotation quotient. The orbit Fintype instance remains. The cochain construction uses these primitive and orbit charts; fixed-period finiteness in the preserved original application belongs to that application.

**Theorem 1.2 (Both chart corrections of a rectangular positive letter).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.positive_gyration`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.positive_gyration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F and H be the literal endpoint presentations, R a natural counted matrix of size n by m, S of size m by n, old a full graph relabel from counted R*S to F.graph, and next one from counted S*R to H.graph. For any d with NeZero d, wordMap of this positive letter is the composition of chartComparison old inverse, the actual elementary R,S map, and chartComparison next. Its gyration is negative old-chart gyration plus relativeForwardGyration R S plus next-chart gyration. Neither comparison is assumed to vanish. n and m may be zero; no inverse of R, S or a time map is required.

**Theorem 1.3 (Composition gives the same endpoint-typed cochain).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.word_gyration`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.word_gyration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cochain is defined recursively on the actual Word F H. A relabel leaf contributes relabelMap gyration; a positive leaf contributes the three terms of positive_gyration; composition adds values. wordMap_comp proves the endpoint-chart cancellation on histories before TimedEquiv.gyration_comp is used. Induction gives wordMap gyration equals cochain for every Word and every nonzero d. There is no arbitrary-homeomorphism leaf, no inverse-recoding leaf, and no replacement by a word in residues.

**Theorem 1.4 (Signed time acts by the actual primitive-orbit count).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.time_corrected_word`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.time_corrected_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a loop w : Word F F, integer s, history equivalence h, time commutation ht at every integer t and actual history x, and hh asserting h x = time F.graph s (w.eval x) for every x, historyGyration h ht d equals cochain d w plus card(Orbit F d) times s in ZMod d. This is a consequence of the actual factorization hh, not of the number of positive letters. inCharts conjugates the full history action into the same fixed chart at both ends; the time-equivariance identities and TimedEquiv.gyration_time determine the sign.

**Theorem 1.5 (Primitive agreement of actual history maps suffices).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.historyGyration_congr_on_primitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.historyGyration_congr_on_primitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two history equivalences h and k commuting with every integer time, agreement on every Primitive F d gives equality of historyGyration at d. The proof transfers that agreement through the same primitiveChart and uses TimedEquiv.gyration_congr. The preserved original application applies this at three and six: a true period-three history is fixed by the forward shift to the sixth power, so agreement on the literal Fix(T^6) domain controls both terms of the same character.

The periodic transport uses actual primitive histories and the existing orbit representatives. Composition and conjugacy laws refer to the same time-equivariant maps; they do not erase endpoint phases of an open edge.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.chart`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.historyGyration_congr_on_primitive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.positive_gyration`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.time_corrected_word`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.word_gyration`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport](CountedRelativeGyrationTransport.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord](TypedPositiveSplitWord.md)
