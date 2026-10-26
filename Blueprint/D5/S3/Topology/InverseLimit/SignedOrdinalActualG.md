# One clopen for every signed lift

## Abstract

Quantitative oscillation on actual successor spaces

**Definition 1.1 (The selected clopen on the successor).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.clopen`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.clopen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assume the continuum hypothesis and fix any actual stage a. Let L be the carrier of finalPrefix at nextStage a. The homeomorphism successorHomeomorph sends L to the coordinate carrier of the same selected Result of run a. The clopen B is the inverse image of that Result's quantitativeClopen under this homeomorphism.

**Definition 1.2 (The original fixed natural columns).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.column`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.column` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural index at q is the n field of column q in the same selected Result. Both this sequence and B depend only on the stage and the fixed run, independently of any signed lift sequence.

**Theorem 1.3 (Strict increase of the fixed columns).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.column_strictMono`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.column_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed natural column sequence is strictly increasing, by the original Result's k_mono law.

**Theorem 1.4 (Every signed norm-one lift has the fixed parity values).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.quantitative_g`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.quantitative_g` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual stage a, let s be any complete sequence of signed measures on L. Assume each s n has total variation one and, for every natural n, its pushforward along the literal restriction from nextStage a to eventRow a equals actualBirth at eventRow a, measured at eta a and n. For every q, even q gives s at column q evaluated on B strictly greater than one sixth; odd q gives exactly zero.

The selected projection identity on the final limit extends to all of L by projection surjectivity and factorization. Together with selected_measure, this identifies every pushed signed measure with the original selected Q measure, at the unchanged eta. The successor homeomorphism preserves total variation and identifies evaluation on the two clopens. Applying the original quantitative_g therefore gives the estimates on L. No positivity or regularity assumption is needed, so arbitrary regular signed lift sequences are included.

**Theorem 1.5 (Both requested value sets are infinite).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.infinite_values`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.infinite_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same all-natural pushforward and norm-one hypotheses, the natural indices n where s n of B is at least one sixth form an infinite set, and the natural indices where s n of B is zero also form an infinite set. The injective images of q under column of twice q and column of twice q plus one lie in these respective sets.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.clopen`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.column`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.column_strictMono`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.infinite_values`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualG.quantitative_g`
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex](SignedOrdinalActualReindex.md)
