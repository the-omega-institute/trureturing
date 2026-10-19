# Endpoint-typed finite positive words with explicit corrections

## Abstract

Endpoint-typed finite positive words with explicit corrections.

Word F H has exactly relabel, positive and comp constructors. A positive letter carries R,S together with actual finite graph relabelings from counted RS and SR to the endpoint presentations. Composition is indexed by its actual intermediate Presentation. Word.eval composes the resulting homeomorphisms, and Word.letters counts positive letters while relabels count zero.

Word.eval_time derives integer-time equivariance by induction over this syntax. Word.numbered_letter recovers the original counted elementaryHomeomorph in the two charts; Word.inverse_letter replaces its inverse by the opposite positive letter with a -1 correction. The outgoing/incoming words use the supplied edge numberings. outgoing_literal has no correction, outgoing_inverse_literal has -1, incoming_literal has -1, and incoming_inverse_literal has no correction. Those are derived equations for every original history, not input assumptions or new inverse/time/arbitrary-homeomorphism constructors.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Definition 1.1 (eval).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.eval`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.eval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the endpoint-typed syntax by composing actual relabel homeomorphisms and positive elementary recodings. Every intermediate graph remains the specified presentation.

**Theorem 1.2 (eval_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.eval_time`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.eval_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction over relabel, positive and composition constructors proves signed-time equivariance of every evaluated word. It is derived from the leaf laws.

**Remark 1.3 (Word).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.Word`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive letter is bracketed by actual finite graph bijections. Composition is indexed by the literal intermediate finite presentation.

**Remark 1.4 (letters).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.letters`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.letters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count positive constructors and add under composition; graph relabels count zero. This measures the constructed word independently of its time correction.

**Remark 1.5 (identity).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.identity`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.identity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the identity graph relabel as the zero-letter word at a presentation. No additional homeomorphism constructor is needed.

**Remark 1.6 (numbered_letter).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.numbered_letter`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.numbered_letter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the two actual endpoint charts, evaluating one positive letter is the original counted elementary homeomorphism. The chart maps are retained explicitly.

**Remark 1.7 (inverse_letter).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.inverse_letter`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.inverse_letter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Opposite POSITIVE letter, with the literal negative-unit correction.

**Remark 1.8 (outOld).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outOld`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outOld` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outgoing supplier has finite edge bijections and both endpoint laws. Expose those as Relabel data; do not introduce another enumeration.

**Remark 1.9 (outNext).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outNext`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outNext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Package the outgoing supplier's numbered new-edge map and vertex numbering as the target graph relabel for a positive letter.

**Remark 1.10 (out_old_number).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.out_old_number`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.out_old_number` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Function-level equalities, including the existing supplier's exact parallel-edge numbering; no matrix-equality transport is hidden here.

**Remark 1.11 (out_next_number).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.out_next_number`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.out_next_number` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The target chart inverse equals the existing outgoing newPaths numbering on every history. This aligns the word chart with the supplied edge enumeration.

**Remark 1.12 (outgoing).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoing`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct the outgoing traversal as one positive letter in its actual old and new charts. Its evaluation has no time correction.

**Remark 1.13 (outgoingBack).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoingBack`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoingBack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the opposite positive letter to traverse the outgoing split backwards. The later literal law retains its negative unit correction.

**Remark 1.14 (incoming).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incoming`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incoming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct the incoming traversal in the supplied incoming charts. Its literal lift requires a negative unit translation of this positive word.

**Remark 1.15 (incomingBack).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incomingBack`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incomingBack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the opposite incoming positive letter for reverse traversal. In this direction the literal forget law needs no time correction.

**Remark 1.16 (outgoing_literal).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoing_literal`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoing_literal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outgoing word evaluates to the actual outgoing lift on every history. This is the unshifted forward case in tower accounting.

**Remark 1.17 (outgoing_inverse_literal).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoing_inverse_literal`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoing_inverse_literal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Outgoing forget is the reverse positive word followed by negative unit time. This is the outgoing contribution to backward correction counts.

**Remark 1.18 (incoming_literal).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incoming_literal`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incoming_literal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Incoming lift is the forward positive word followed by negative unit time. This is the incoming contribution to forward correction counts.

**Remark 1.19 (incoming_inverse_literal).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incoming_inverse_literal`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incoming_inverse_literal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Incoming forget equals the reverse positive word without a correction. This completes the four literal split-direction laws.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.Word`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.eval`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.eval_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.identity`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incoming`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incomingBack`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incoming_inverse_literal`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.incoming_literal`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.inverse_letter`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.letters`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.numbered_letter`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outNext`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outOld`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.out_next_number`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.out_old_number`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoing`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoingBack`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoing_inverse_literal`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord.outgoing_literal`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation](SplitTowerTranslation.md)
