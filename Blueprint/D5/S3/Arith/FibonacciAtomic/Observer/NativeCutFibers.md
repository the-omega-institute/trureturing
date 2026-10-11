# NativeCutFibers

## Abstract

NativeCutFibers

**Definition 1.1 (Actually occurring old classes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.labels`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.labels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite support contains exactly the names retained in the actual old row. No unused Nat coordinates become extra source information.

**Definition 1.2 (Complete legal old-class valuations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.LegalValues`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.LegalValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One value is reused at every occurrence of an old class. Injectivity on the entire appearing class set preserves every cross-class disequality, including classes outside the new cones.

**Theorem 1.3 (Actual old-row reconstruction).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall u: Source, (\forall v: \operatorname{LegalValues}\left(\operatorname{canonicalRow}\left(P, u\right)\right), (\operatorname{canonicalRow}\left(P, \operatorname{evaluateRow}\left(\operatorname{extend}\left(\operatorname{canonicalRow}\left(P, u\right), \operatorname{val}\left(v\right)\right), \operatorname{canonicalRow}\left(P, u\right)\right)\right) = \operatorname{canonicalRow}\left(P, u\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.legal_values_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Filling an actual canonical row by any entire legal valuation returns the same canonical row. The independent addressed exterior and full partition record prove the bridge. Every absent public cut retains its concrete original leaf guard.

**Definition 1.4 (Entire actual old-row fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.RowFiber`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.RowFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is every actual original Boolean tree with the specified canonicalRow, without a size bound, sample restriction or product-fiber premise.

**Definition 1.5 (Mathematical inverse valuation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.recover`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.recover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse recovers actual class values from an original source in the fiber. This proof operation is not an accessible source identity or subtree-equality service port.

**Definition 1.6 (Exact old-class/source equivalence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.rowFiberEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.rowFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation and recovery are mutually inverse and evaluation is injective on legal valuations. The complete actual row, rather than a supplied factorization hypothesis, determines the fiber.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.LegalValues`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.RowFiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.labels`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.legal_values_row`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.recover`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.rowFiberEquiv`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation](NativeGroundSeparation.md)
