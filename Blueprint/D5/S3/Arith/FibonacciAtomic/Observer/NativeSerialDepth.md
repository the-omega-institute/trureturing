# NativeSerialDepth

## Abstract

NativeSerialDepth

**Definition 1.1 (Finite whole-row output representation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.RowWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.RowWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite list of optional Boolean-or-natural labels represents the complete row, including concrete exterior constructors and canonical hole class labels.

**Definition 1.2 (Injective preorder row encoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.rowWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.rowWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each leaf is one tagged label and each binary constructor is a separate marker. Prefix parsing proves injectivity without a tree-size bound; the encoding is used to transfer the original effective finite-output service to the complete canonical row.

**Theorem 1.3 (Full original-service depth and whole-output image).**

$$\forall S: \operatorname{OriginalEffectiveService}\left(RowWord\right), (\forall s: OriginalState, (\forall P, Q: CutSet, ((\operatorname{CutPrefixFree}\left(Q\right)) \implies (\forall old: LiteralRow, (\forall H: History, (\forall N, K: Nat, ((\operatorname{epoch}\left(s\right) = N) \implies ((\operatorname{Nonempty}\left(\operatorname{ActualFiber}\left(P, old, H\right)\right)) \implies ((\forall u: \operatorname{ActualFiber}\left(P, old, H\right), (\exists t: Trace, ((\operatorname{OriginalRun}\left(S, s, \operatorname{iterate}\left(substitution, N, \operatorname{value}\left(u\right)\right), t, \operatorname{rowWord}\left(\operatorname{canonicalRow}\left(Q, \operatorname{value}\left(u\right)\right)\right)\right)) \land (\operatorname{length}\left(\operatorname{answers}\left(t\right)\right) \leq K)))) \implies ((\exists h: Nat, (\forall u, v: \operatorname{ActualFiber}\left(P, old, H\right), ((\operatorname{OriginalAgree}\left(h, \operatorname{value}\left(u\right), \operatorname{value}\left(v\right)\right)) \implies ((\operatorname{canonicalRow}\left(Q, \operatorname{value}\left(u\right)\right) = \operatorname{canonicalRow}\left(Q, \operatorname{value}\left(v\right)\right)) \land (\operatorname{literalRecord}\left(Q, \operatorname{value}\left(u\right)\right) = \operatorname{literalRecord}\left(Q, \operatorname{value}\left(v\right)\right)))))) \land (\exists labels: \operatorname{Finset}\left(LiteralRow\right), ((\operatorname{card}\left(labels\right) \leq \operatorname{pow}\left(4, K\right)) \land (\forall u: \operatorname{ActualFiber}\left(P, old, H\right), (\operatorname{canonicalRow}\left(Q, \operatorname{value}\left(u\right)\right) \in labels))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.original_whole_row_implies_depth_and_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original selector simulation feeds the unrestricted native depth and prefix-free output-image theorems. The domain remains the entire ActualFiber, with one shared finite selector state at the actual epoch N and initial physical register substitution iterated N times on u. The common state may encode the complete retained row, task input, accessible workspace and any genuinely retained prior chronological record. It is not identified with H: H retains mixed-epoch Read constraints, while the selector appends the new chronological external suffix. Under original 59.3 the complete takeover state is a deterministic function of common input and R and recovers R; original 62.2 gives equal reached state on the same actual continuation record, and 74.1 exhausts accessible source information by U. Consequently this single state is common to the full fiber, rather than adding an extra producer-record filter. The frozen canonicalRow_record_iff, rowFiberEquiv and historyCellEquiv identify R with the complete exterior/full partition and H with its literal constraints, retaining all cross-class disequalities, repeated occurrences and absent guards. Producer acquisition records excluded by 59.3 are never reinstated. Certified N at least every historical epoch is an allowed specialization of this stronger unconstrained-N theorem. Injective finite row coding yields equality of whole canonicalRow and literalRecord, and at most four to the K terminal whole rows, including K zero and root/empty cuts. The proof-only image decoder supplies no runtime oracle. The original partial selector has sourcewise finite executions; no common local-work, runtime, update, workspace or address bound is assumed.

**Theorem 1.4 (Labeled native trace and full-output uniqueness).**

$$\forall C, O: Type, (\forall delta: C \to \operatorname{Op}\left(C, O\right), (\forall c: C, (\forall e: Nat, (\forall r: Source, (\forall t, s: Trace, (\forall o, p: O, (((\operatorname{Run}\left(delta, c, e, r, t, o\right)) \land (\operatorname{Run}\left(delta, c, e, r, s, p\right))) \implies ((t = s) \land (o = p)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.run_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two NativeSerialMachine.Run proofs from the same program, control, epoch and source have equal complete labeled traces and equal full outputs. The original statement and induction are preserved. OriginalVector.InterleavedWordRecovery consumes this theorem for the constructed vertex and word runs; it adds no execution interface or unlabeled halt semantics.

**Definition 1.5 (Complete original-prefix agreement).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.OriginalAgree`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.OriginalAgree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Agreement quantifies over every original address of length at most the given radius and uses the actual four-valued readout, including absence.

**Definition 1.6 (Proof-only descriptor selection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.descriptor`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.descriptor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite replay, when it exists at a Read boundary, determines its unique epoch and physical address. A classical default on other words is used only to form a finite image. It supplies no effective stationary service.

**Theorem 1.7 (Finite actual physical support).**

$$\forall C, O: Type, (\forall delta: C \to \operatorname{Op}\left(C, O\right), (\forall c: C, (\forall N, K: Nat, (\exists D: \operatorname{Finset}\left(Descriptor\right), (\forall u: Source, (\forall t: Trace, (\forall o: O, ((\operatorname{Run}\left(delta, c, N, \operatorname{iterate}\left(substitution, N, u\right), t, o\right)) \implies ((\operatorname{length}\left(\operatorname{answers}\left(t\right)\right) \leq K) \implies (\forall n: Nat, (\forall a: Address, (\forall y: Reply, ((\operatorname{ReadEvent}\left(n, a, y\right) \in t) \implies (\operatorname{tuple}\left(n, a\right) \in D))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.bounded_read_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Four-valued reply words of length strictly less than K form a finite set. Actual Read boundaries are uniquely determined by these words, so their physical epoch-address descriptors lie in one finite set. This does not assume finite control, a finite source fiber, bounded addresses or bounded update counts.

**Theorem 1.8 (Finite original observation depth).**

$$\forall C, O: Type, (\forall delta: C \to \operatorname{Op}\left(C, O\right), (\forall c: C, (\forall N, K: Nat, (\forall U: \operatorname{Set}\left(Source\right), (\forall F: Source \to O, ((\forall u: Source, ((u \in U) \implies (\exists t: Trace, ((\operatorname{Run}\left(delta, c, N, \operatorname{iterate}\left(substitution, N, u\right), t, \operatorname{F}\left(u\right)\right)) \land (\operatorname{length}\left(\operatorname{answers}\left(t\right)\right) \leq K))))) \implies (\exists h: Nat, (\forall u: Source, ((u \in U) \implies (\forall v: Source, ((v \in U) \implies ((\operatorname{OriginalAgree}\left(h, u, v\right)) \implies ((\operatorname{F}\left(u\right) = \operatorname{F}\left(v\right)) \land (\exists t: Trace, ((\operatorname{Run}\left(delta, c, N, \operatorname{iterate}\left(substitution, N, u\right), t, \operatorname{F}\left(u\right)\right)) \land (\operatorname{Run}\left(delta, c, N, \operatorname{iterate}\left(substitution, N, v\right), t, \operatorname{F}\left(v\right)\right)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.bounded_serial_original_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the maximum address length in the finite physical support, with maximum zero for an empty support. All-epoch original-prefix locality makes every physical reply agree on sources with the same original prefix. Actual execution transfer then preserves the entire local/update/read trace and complete output. The radius can depend on the program, common input, fiber and initial epoch; no bound depending only on K and no common radius for all initial epochs is asserted.

**Theorem 1.9 (Whole actual row and record).**

$$\forall C: Type, (\forall delta: C \to \operatorname{Op}\left(C, LiteralRow\right), (\forall c: C, (\forall P, Q: CutSet, ((\operatorname{CutPrefixFree}\left(Q\right)) \implies (\forall old: LiteralRow, (\forall H: History, (\forall N, K: Nat, ((\forall u: \operatorname{ActualFiber}\left(P, old, H\right), (\exists t: Trace, ((\operatorname{Run}\left(delta, c, N, \operatorname{iterate}\left(substitution, N, \operatorname{value}\left(u\right)\right), t, \operatorname{canonicalRow}\left(Q, \operatorname{value}\left(u\right)\right)\right)) \land (\operatorname{length}\left(\operatorname{answers}\left(t\right)\right) \leq K)))) \implies (\exists h: Nat, (\forall u, v: \operatorname{ActualFiber}\left(P, old, H\right), ((\operatorname{OriginalAgree}\left(h, \operatorname{value}\left(u\right), \operatorname{value}\left(v\right)\right)) \implies ((\operatorname{canonicalRow}\left(Q, \operatorname{value}\left(u\right)\right) = \operatorname{canonicalRow}\left(Q, \operatorname{value}\left(v\right)\right)) \land (\operatorname{literalRecord}\left(Q, \operatorname{value}\left(u\right)\right) = \operatorname{literalRecord}\left(Q, \operatorname{value}\left(v\right)\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.whole_row_serial_implies_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain is the entire NativeHistoryCells.ActualFiber of the complete old canonical row and mixed-epoch history. All old inequalities, repeated classes and absent-cut guards are retained by that interface. The conclusion concerns the complete new canonicalRow and the independently computed literalRecord, including exterior and whole partition. Arbitrary finite cuts, root and empty cuts, and finite nonempty fibers remain included. No ground-binding or unification premise occurs. The result is valid even without nonemptiness, and at every fixed actual common epoch.

**Theorem 1.10 (Encoded effective serial clause implies finite depth).**

$$\forall S: \operatorname{EffectiveService}\left(LiteralRow\right), (\forall P, Q: CutSet, ((\operatorname{CutPrefixFree}\left(Q\right)) \implies (\forall old: LiteralRow, (\forall H: History, (\forall N, K: Nat, ((\forall u: \operatorname{ActualFiber}\left(P, old, H\right), (\exists t: Trace, ((\operatorname{ServiceRun}\left(S, \operatorname{initial}\left(S\right), N, \operatorname{iterate}\left(substitution, N, \operatorname{value}\left(u\right)\right), t, \operatorname{canonicalRow}\left(Q, \operatorname{value}\left(u\right)\right)\right)) \land (\operatorname{length}\left(\operatorname{answers}\left(t\right)\right) \leq K)))) \implies (\exists h: Nat, (\forall u, v: \operatorname{ActualFiber}\left(P, old, H\right), ((\operatorname{OriginalAgree}\left(h, \operatorname{value}\left(u\right), \operatorname{value}\left(v\right)\right)) \implies ((\operatorname{canonicalRow}\left(Q, \operatorname{value}\left(u\right)\right) = \operatorname{canonicalRow}\left(Q, \operatorname{value}\left(v\right)\right)) \land (\operatorname{literalRecord}\left(Q, \operatorname{value}\left(u\right)\right) = \operatorname{literalRecord}\left(Q, \operatorname{value}\left(v\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.effective_whole_row_implies_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the exact encoded-service inclusion to the full actual fiber and whole-row output. Sourcewise stopping and one uniform chronological Read budget then give precisely the finite-original-depth implication, without any stationary-service construction or other direction of the four-way classification.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.OriginalAgree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.RowWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.bounded_read_support`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.bounded_serial_original_depth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.descriptor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.effective_whole_row_implies_depth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.original_whole_row_implies_depth_and_image`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.rowWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.run_unique`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.whole_row_serial_implies_depth`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells](NativeHistoryCells.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective](NativeSerialEffective.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialImage](NativeSerialImage.md)
