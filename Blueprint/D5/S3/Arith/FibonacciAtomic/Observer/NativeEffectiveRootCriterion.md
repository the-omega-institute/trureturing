# Effective Native Birth Provenance Criterion

## Abstract

The complete same-capacity coloring criterion and the particular acquired encoder and stationary reader.

Acquisition, authentication, actual complete export, lawful common entry, installation, and isolation remain the paid premises of Assumption 10.6. The program does not establish these physical or authority conditions.

Zero classes, zero calls, empty color cells, repeated occurrences, unused colors, and impossible branches remain in scope. The original feasibility predicate permits infinite ambient payload carriers with finite actual encoder range. The criterion preserves that original domain through the retained full feasibility equivalence.

The formulas suppress erased proof arguments to acquiredEncoder and coerce values and origins to their underlying data. Rho denotes substitution, and emptyList is the empty colored table.

**Definition 1.1 (Complete Finite Coloring Enumeration).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.colorings`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.colorings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List.pi enumerates all functions from the executable attained chart to Fin r. Unused colors are allowed.

**Definition 1.2 (Exact Colored-Cell Test).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.colorPasses`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.colorPasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only nonempty color cells impose a minimax budget test. The unit-call value is computed on the actual class-root menu, with q unchanged.

**Definition 1.3 (Executable Finite Decision and Package).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.decideNative`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.decideNative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The program searches the finite colorings and returns their color map with the actual minimax trees. Its data inputs are the finite row, r, and q; source and word bounds and actual origins are absent.

**Theorem 1.4 (Full Corollary 10.9 and NBP.10.13).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall C: LiteralRow, ((\operatorname{Nonempty}\left(\operatorname{OriginFiber}\left(P, C\right)\right)) \implies (\forall r, q: Nat, ((1 \leq r) \implies (((\operatorname{isSome}\left(\operatorname{decideNative}\left(C, r, q\right)\right) = true) \iff (\operatorname{InvFeas}\left(P, C, r, q\right))) \land ((\operatorname{InvFeas}\left(P, C, r, q\right)) \iff (\exists c: (\operatorname{Chart}\left(C\right)) \to (\operatorname{Fin}\left(r\right)), (\forall i: \operatorname{Fin}\left(r\right), ((\operatorname{coloredRows}\left(c, i\right) \neq emptyList) \implies (\operatorname{minimaxValue}\left(C, \operatorname{coloredRows}\left(c, i\right)\right) \leq q)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.effective_native_birth_provenance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite cut set, prefix-free cut condition, complete row with nonempty actual image fiber, r at least one, and arbitrary natural q, a positive decision is equivalent to original InvFeas at the same r and q. Original InvFeas is also equivalent to a coloring whose every nonempty cell has minimax value at most q. NativeFullRootFeasibility.native_full_root_feasibility is applied directly.

**Definition 1.5 (Encoder from Actually Acquired Values).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.acquiredEncoder`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.acquiredEncoder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The encoder applies the returned color map to the roots of the actually acquired class values. The row-validity and nonempty-origin premises are propositions erased by code generation; no actual origin is a runtime data argument.

**Definition 1.6 (Representative-Address Installation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.nativeEntry`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.nativeEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NativeFullRootFeasibility.install compiles the selected finite tree to native calls at row-determined representatives. The unreachable fourth reply stops immediately. No equality or source-feasibility operation exists in this dialogue.

**Theorem 1.7 (Correctness of the Particular Positive Output).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall C: LiteralRow, ((\operatorname{Nonempty}\left(\operatorname{OriginFiber}\left(P, C\right)\right)) \implies (\forall r, q: Nat, ((1 \leq r) \implies (\forall pkg: \operatorname{RootPackage}\left(C, r\right), ((\operatorname{decideNative}\left(C, r, q\right) = \operatorname{some}\left(pkg\right)) \implies ((\operatorname{Finite}\left(\operatorname{range}\left(\operatorname{acquiredEncoder}\left(P, C, pkg\right)\right)\right)) \land (\operatorname{ncard}\left(\operatorname{range}\left(\operatorname{acquiredEncoder}\left(P, C, pkg\right)\right)\right) \leq r) \land (\forall v: \operatorname{ImageValues}\left(C\right), (\forall u: \operatorname{OriginFiber}\left(P, C\right), ((\operatorname{rho}\left(u\right) = \operatorname{evaluateRow}\left(\operatorname{extend}\left(C, v\right), C\right)) \implies (\exists tr: Trace, ((\operatorname{Run}\left(controller, \operatorname{nativeEntry}\left(C, pkg, \operatorname{acquiredEncoder}\left(P, C, pkg, v\right)\right), 0, \operatorname{rho}\left(u\right), tr, \operatorname{canonicalRow}\left(P, u\right)\right)) \land (\operatorname{Stationary}\left(tr\right)) \land (\operatorname{length}\left(\operatorname{answers}\left(tr\right)\right) \leq q))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.returned_native_reader` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual returned package, the acquired encoder has finite range of cardinality at most r. Its installed controller recovers the entire predecessor row in a stationary run with at most q answers on every actual filling and compatible origin. The proof uses the unchanged installation, run, and call-count suppliers and the full factorization theorem.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.acquiredEncoder`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.colorPasses`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.colorings`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.decideNative`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.effective_native_birth_provenance`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.nativeEntry`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.returned_native_reader`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax](NativeFiniteRootMinimax.md)
