# NativeCutFibers

## Abstract

NativeCutFibers

**Definition 1.1 (Actually occurring old classes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.labels`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.labels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite support contains exactly the names retained in the actual old row. No unused Nat coordinates become extra source information.

**Theorem 1.2 (Occurring canonical names).**

$$\forall P: CutSet, (\forall u: Source, (\operatorname{labels}\left(\operatorname{canonicalRow}\left(P, u\right)\right) = \operatorname{image}\left(\operatorname{toFinset}\left(\operatorname{orderedHoles}\left(P, u\right)\right), \operatorname{classOrdinal}\left(P, u\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.labels_canonical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occurring labels of a canonical row are exactly the image of its ordered reached holes under classOrdinal. This identifies the finite set counted in NativeSharpPredecessorFiber without assuming consecutive raw ordinals.

**Definition 1.3 (Complete legal old-class valuations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.LegalValues`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.LegalValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One value is reused at every occurrence of an old class. Injectivity on the entire appearing class set preserves every cross-class disequality, including classes outside the new cones.

**Theorem 1.4 (Actual old-row reconstruction).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall u: Source, (\forall v: \operatorname{LegalValues}\left(\operatorname{canonicalRow}\left(P, u\right)\right), (\operatorname{canonicalRow}\left(P, \operatorname{evaluateRow}\left(\operatorname{extend}\left(\operatorname{canonicalRow}\left(P, u\right), \operatorname{val}\left(v\right)\right), \operatorname{canonicalRow}\left(P, u\right)\right)\right) = \operatorname{canonicalRow}\left(P, u\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.legal_values_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Filling an actual canonical row by any entire legal valuation returns the same canonical row. The independent addressed exterior and full partition record prove the bridge. Every absent public cut retains its concrete original leaf guard.

**Definition 1.5 (Entire actual old-row fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.RowFiber`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.RowFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is every actual original Boolean tree with the specified canonicalRow, without a size bound, sample restriction or product-fiber premise.

**Theorem 1.6 (Recovery Reconstructs Every Actual Source).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall C: LiteralRow, (\forall u: \operatorname{RowFiber}\left(P, C\right), (\operatorname{evaluateRow}\left(\operatorname{extend}\left(C, \operatorname{val}\left(\operatorname{recover}\left(P, C, u\right)\right)\right), C\right) = \operatorname{val}\left(u\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.recover_fill` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite prefix-free cut, every complete row C and every source u in its row fiber, filling C with the recovered class valuation gives exactly u. The source carrier remains unrestricted. This mathematical reconstruction is not a physical port.

**Definition 1.7 (Mathematical inverse valuation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.recover`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.recover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse recovers actual class values from an original source in the fiber. This proof operation is not an accessible source identity or subtree-equality service port.

**Definition 1.8 (Exact old-class/source equivalence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.rowFiberEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.rowFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation and recovery are mutually inverse and evaluation is injective on legal valuations. The complete actual row, rather than a supplied factorization hypothesis, determines the fiber.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.LegalValues`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.RowFiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.labels`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.labels_canonical`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.legal_values_row`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.recover`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.recover_fill`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.rowFiberEquiv`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation](NativeGroundSeparation.md)
