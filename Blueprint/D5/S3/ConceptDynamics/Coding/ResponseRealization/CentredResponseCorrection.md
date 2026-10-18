# Centring the actual numbered response history

## Abstract

The numbered response lift is uncentred by a forward translation and recovered by the literal negative centring correction.

Let V and E be arbitrary finite types, with decidable vertex equality and a discrete topology on E. G is a directed multigraph and pair is a TablePair G G a b c d, with arbitrary natural radii, including zero. No Essential G or SameTableConjugacy is needed for these input-lift identities. Histories are indexed by all integers. The existing translate G s reads the old history at t+s; this sign convention is used literally throughout.

Write L for OriginalResponseNumbering.numberedLift and U for uncentred. The definition is U(x)=L(translate G a x); its inverse first decodes L and then translates by -a. The coordinate proof cancels the existing finite edge encoding and compares every coordinate of the retained legal word. U(x) at t therefore decodes to the complete word from t through t+a+b+1, including both endpoints. Recovering L(x) requires U(translate G (-a) x).

These coordinate identities keep later positive recodings on the same original histories and at the same time origin. FullOutResponseIdentification.agrees_existing_uncentred connects the constructed repeated input lift to this uncentred lift.

**Remark 1.1 (uncentred).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection.uncentred`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection.uncentred` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual homeomorphism is built from the existing numbered lift and integer translations, including both inverse and continuity proofs. It is used by all coordinate and centring statements and by the later input identification. Its construction adds no new response numbering.

**Theorem 1.2 (uncentred_coordinate).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection.uncentred_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection.uncentred_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original history x and every integer t, decoding U(x) at t gives makeEdge of historyWindow G x t (a+b+1+1). This compares full legal words and preserves parallel-edge identities. FullOutResponseIdentification.agrees_existing_uncentred uses this coordinate identity. The same coordinates also derive signed-time commutation locally.

**Theorem 1.3 (centred_eq_uncentred_negative).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection.centred_eq_uncentred_negative`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection.centred_eq_uncentred_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every history x, numberedLift G pair x equals U applied to translate G (-a) x. Expanding the two translations cancels a with -a coordinatewise. FullOutResponseIdentification.numberedLift_eq_repeated_negative consumes this equation; substitution into the centred response equality also derives the uncentred consequence locally.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection.centred_eq_uncentred_negative`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection.uncentred`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection.uncentred_coordinate`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseGraphs/OriginalResponseGraph](../ResponseGraphs/OriginalResponseGraph.md)
