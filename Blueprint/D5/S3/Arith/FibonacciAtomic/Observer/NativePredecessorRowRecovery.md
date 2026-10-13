# Native predecessor-row recovery

## Abstract

NativePredecessorRowRecovery

**Definition 1.1 (Old reached occurrences).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.H`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H extracts the finite hole-address set from the entire canonical old row. The existing literalRow_hole_support and canonicalRow_reached identify it with the reached public cuts. Empty cuts, root cuts and absent deeper cuts are included.

**Definition 1.2 (Substitution with opaque markers).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.sigma`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native Source is FreeMagma Bool, with true alpha and false beta. Opaque substitution sends concrete alpha to beta and concrete beta to the ordered pair of beta and alpha. Every equality-class marker is fixed, and every ordered bracket is retained.

**Definition 1.3 (Repair at actual occurrence addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.repairAt`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.repairAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite traversal carries its current address. An occurrence in the supplied old set stays an opaque marker, renamed by ActualCutPartitionDecoder.decoderClass on that restricted support. A newborn marker is restored to beta at a final false edge and alpha at a final true edge. A newborn root is rejected. Concrete leaves and ordered pairs retain their syntax. Decisions use occurrence membership even when an old and a newborn occurrence share one current class. Class names are first-hole ordinals and can be sparse.

**Definition 1.4 (Whole-row repair).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.repair`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.repair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Repair starts the address traversal at the root. On an actual one-step transition, contextual induction over the original source proves repair of the current row equals opaque substitution of the old canonical row. Old cut stops use equality-kernel preservation under the existing injective native substitution and idxOf_map_relation. An alpha leaf produces beta. A beta leaf produces a beta/alpha pair whose separately optional child cuts are restored by their final edges. A source pair recursively preserves both sides. Prefix freedom permits descent without a strict cut ancestor.

**Definition 1.5 (Finite opaque image parsing).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.delta`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Beta parses to alpha, a bare alpha fails, and an opaque marker stays fixed. The exact ordered beta/alpha pair parses to beta before the general-pair rule recursively parses both children. An opaque substitution image cannot be a concrete alpha, so the special block cannot collide with a pair of opaque images. Structural induction proves parsing after opaque substitution returns the entire input term.

**Definition 1.6 (Uniform partial predecessor decoder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.back`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.back` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Back composes repair with opaque parsing. Its runtime arguments are only the current LiteralRow and old reached CutSet; it receives no source, source value, alpha-class supplement, rank or depth bound. Finite structural recursion terminates, with no further complexity claim.

**Theorem 1.7 (Exact recovery and conditional equivalence).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies ((\forall v: Source, (\operatorname{back}\left(\operatorname{canonicalRow}\left(P, \operatorname{substitution}\left(v\right)\right), \operatorname{H}\left(P, v\right)\right) = \operatorname{some}\left(\operatorname{canonicalRow}\left(P, v\right)\right))) \land (\forall v, w: Source, ((\operatorname{canonicalRow}\left(P, \operatorname{substitution}\left(v\right)\right) = \operatorname{canonicalRow}\left(P, \operatorname{substitution}\left(w\right)\right)) \implies ((\operatorname{canonicalRow}\left(P, v\right) = \operatorname{canonicalRow}\left(P, w\right)) \iff (\operatorname{H}\left(P, v\right) = \operatorname{H}\left(P, w\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.native_predecessor_row_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite prefix-free public cut and every finite native source, Back returns exactly some of the old canonical row after one actual native substitution. The complete exterior, all reached occurrences, the entire equality/disequality partition and absent-cut guards are therefore recovered. For two actual sources with equal current rows, their old rows agree exactly when their old reached sets agree. The forward implication extracts support; the reverse uses identical decoder inputs and exact recovery. The original-present transport supplier is NativeDepthPatterns.original_present_transport at epoch one. Source injectivity is reused from SourceTransportCentralizer.source_transport_centralizer. Neither full-image choice inversion nor common-suffix recutting is a runtime operation. Successful parsing of an alleged row and set certifies no physical provenance, continuity, origin or inverse action. These are source-specific deductions using known finite syntax and partition methods, with no claim of literature priority.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.H`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.back`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.delta`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.native_predecessor_row_recovery`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.repair`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.repairAt`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.sigma`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](../SourceTransportCentralizer.md)
