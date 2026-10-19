# Identify the full outgoing input with the numbered response

## Abstract

Repeated full outgoing splits identify with the original response graph and its unchanged finite edge numbering on every history.

F is any TwoSidedFiniteInduction.Presentation, with its actual graph, finite carriers, essentiality and discrete edge topology. pair is a TablePair F.graph F.graph a b c d for arbitrary natural a,b,c,d. Write q=a+b+1. RepeatedFullOutSplit.stage F q is the actual q-fold full outgoing split with partition id. Its previously constructed identification has vertices the legal q-words and edges the legal (q+1)-words. No graph equivalence or desired history equality is an input.

wordResponse retains the full original legal word and attaches the forced pair.f response to its prefix. Composing that finite equivalence with the q-stage identification gives responseIdentification, with both endpoint equations. response_coordinate uses flatten_window on the actual repeated lift. The private numbering then uses the existing vertexNumber and the inverse of the existing edgeEquiv. numberedIdentification preserves every original parallel-edge number; it defines no replacement matrix or enumerator.

The endpoint-preserving numberedIdentification includes all parallel-edge identities and zero fibers. Restrict its bijection to any endpoint subtype; vertex injectivity proves the inverse endpoint equations. Fintype.card_congr then gives equal endpoint cardinalities, and card_eq_zero_iff identifies emptiness. This is a local consequence of the retained full bijection, including empty carriers.

uncentredRepeatedLift is defined first by the actual repeated lifts followed by the constructed numbered graph homeomorphism. Its decoded coordinates give exactly the future block [t,t+a+b+1]. Comparing with CentredResponseCorrection.uncentred_coordinate yields agrees_existing_uncentred. Composing with the literal -a correction gives numberedLift_eq_repeated_negative and then numberedLift_eq_tower_negative via tower_apply.

OriginalPositiveWordAssembly.positive_word explicitly uses numberedIdentification and numberedLift_eq_tower_negative with F=ResponseTwoSidedConsumer.original G hG. This is an already-written source bridge from the actual input tower to the response-output word, not a missing identification assumption. The source does not itself establish the original-h character, the 2/7 orbit counts, literal Fix(T^6), the same chi obstruction at every 0<n<6, or proof/type axiom closure.

**Remark 1.1 (responseIdentification).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.responseIdentification`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.responseIdentification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the finite vertex and edge relabeling from the actual q-stage full-out graph to the response graph. The private wordResponse inverse retains the original legal word. The retained numberedIdentification and response_coordinate consume this full relabeling.

**Theorem 1.2 (response_coordinate).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.response_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.response_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hist F and integer t, the relabeled repeated lift has exactly the full future response edge. It uses the imported flatten_window identity and is consumed by numbered_coordinate.

**Remark 1.3 (numberedIdentification).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numberedIdentification`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numberedIdentification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Composes the constructed response identification with the existing literal vertex and edge numbering, proving source and target preservation. The original positive-word assembly uses this actual finite Relabel as a word leaf.

**Remark 1.4 (uncentredRepeatedLift).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.uncentredRepeatedLift`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.uncentredRepeatedLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The homeomorphism is the actual repeated full-out lift followed by numberedIdentification.homeomorph. It is not defined by the older U. It feeds numbered_coordinate, agrees_existing_uncentred and the negative-centring handoff.

**Theorem 1.5 (numbered_coordinate).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numbered_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numbered_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Existing numbered decoding cancels exactly, after which response_coordinate supplies the full future word. The equality is consumed by agrees_existing_uncentred.

**Theorem 1.6 (agrees_existing_uncentred).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.agrees_existing_uncentred`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.agrees_existing_uncentred` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compares every integer coordinate after the injective existing edgeEquiv, using the two full-word coordinate formulas. It is used by numberedLift_eq_repeated_negative.

**Theorem 1.7 (numberedLift_eq_repeated_negative).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numberedLift_eq_repeated_negative`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numberedLift_eq_repeated_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replaces the older U by the independently constructed repeated lift and applies the literal negative centring equation. The local tower-form handoff consumes it.

**Theorem 1.8 (numberedLift_eq_tower_negative).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numberedLift_eq_tower_negative`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numberedLift_eq_tower_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uses the imported tower_apply equation to express the same -a identity through the actual Tower evaluator. OriginalPositiveWordAssembly.positive_word explicitly consumes this statement for its original-domain word.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.agrees_existing_uncentred`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numberedIdentification`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numberedLift_eq_repeated_negative`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numberedLift_eq_tower_negative`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.numbered_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.responseIdentification`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.response_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification.uncentredRepeatedLift`
- Dependency: [D5/S3/ConceptDynamics/Coding/FullOutSplitWordIdentification](../FullOutSplitWordIdentification.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph](../PositiveRecoding/FiniteGraphRelabelHomeomorph.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseGraphs/OriginalResponseGraph](../ResponseGraphs/OriginalResponseGraph.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection](CentredResponseCorrection.md)
