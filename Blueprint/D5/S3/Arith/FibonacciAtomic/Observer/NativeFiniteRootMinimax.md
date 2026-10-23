# Finite Actual Root Menu Minimax

## Abstract

Executable attained chart and exact unit-call optimum on the actual three-reply menu.

The actual menu consists only of the classes occurring in the complete current row. The three replies are some true, some false, and none. The fourth native absent reply has no table row.

This natural-number executable optimizer supplies the effective part of Native Birth Provenance Corollary 10.9. It adds no physical-cost or performance claim. Finite normalization and Bellman methods are existing suppliers; the particular row-count-fueled construction and its attaining-tree theorem are the mathematical content here.

In the formula, rowType and rowTarget denote the TableRow projections; chart elements coerce to their assignments. The two Boolean implications express the exact constant versus nonconstant recurrence.

**Definition 1.1 (Attained Type Checker).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.admissibleCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.admissibleCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean image grammar and distinct-class leaf bounds decide precisely Admissible. The branch obligation remains in the retained native image-chart supplier.

**Theorem 1.2 (Exact Boolean Admissibility).**

$$\forall C: LiteralRow, (\forall theta: (\operatorname{Classes}\left(C\right)) \to (\operatorname{Option}\left(Bool\right)), ((\operatorname{admissibleCode}\left(C, theta\right) = true) \iff (\operatorname{Admissible}\left(C, theta\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.admissibleCode_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public equivalence connects the executable checker to the original admissibility predicate for every literal row and every class-root assignment. It is reused by the actual repeated-partner controllers.

**Definition 1.3 (Finite Chart Enumeration).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.chartList`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.chartList` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List.pi enumerates the three replies at every appearing class and filters by admissibleCode. Completeness includes zero classes. No actual origin, source-size bound, or native-word bound is a data argument.

**Definition 1.4 (Entire Predecessor Target).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.computedTarget`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.computedTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The computable mask tests each occurrence parent for the visible alpha sibling and calls NativePredecessorRowRecovery.back. Shared old and new occurrences are repaired individually, including the root and blocked cuts.

**Definition 1.5 (Executable Unit-Call Value).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.minimaxValue`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.minimaxValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Row-count fuel suffices: every nonempty reply fiber of a splitting coordinate is strictly smaller. A constant target costs zero. Otherwise List.argmin selects the actual class coordinate with one plus the maximum child value. Empty reply cells contribute zero.

**Definition 1.6 (Particular Attaining Tree).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.minimaxTree`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.minimaxTree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tree follows the same argmin and three reply cells as minimaxValue. Constant tables stop at their common complete target. Empty and impossible branches stop at the supplied fallback.

**Theorem 1.7 (Exact Recurrence and Finite Chart Bound).**

$$\forall C: LiteralRow, (\forall W: \operatorname{List}\left(\operatorname{TableRow}\left(C\right)\right), ((((\operatorname{constantTarget}\left(W\right) = true) \implies (\operatorname{minimaxValue}\left(C, W\right) = 0)) \land ((\operatorname{constantTarget}\left(W\right) = false) \implies (\operatorname{minimaxValue}\left(C, W\right) = \operatorname{scoreMinimum}\left(C, W, \operatorname{minimaxValue}\left(C\right)\right)))) \land (\forall fallback: LiteralRow, ((\forall a: \operatorname{TableRow}\left(C\right), ((\operatorname{member}\left(a, W\right)) \implies (\operatorname{fst}\left(\operatorname{rootRun}\left(\operatorname{rowType}\left(a\right), \operatorname{minimaxTree}\left(C, fallback, W\right)\right)\right) = \operatorname{rowTarget}\left(a\right)))) \land (\operatorname{rootDepth}\left(\operatorname{minimaxTree}\left(C, fallback, W\right)\right) = \operatorname{minimaxValue}\left(C, W\right)))) \land (\forall T: \operatorname{RootTree}\left(C, LiteralRow\right), ((\forall a: \operatorname{TableRow}\left(C\right), ((\operatorname{member}\left(a, W\right)) \implies (\operatorname{fst}\left(\operatorname{rootRun}\left(\operatorname{rowType}\left(a\right), T\right)\right) = \operatorname{rowTarget}\left(a\right)))) \implies (\operatorname{minimaxValue}\left(C, W\right) \leq \operatorname{rootDepth}\left(T\right)))) \land (\operatorname{length}\left(\operatorname{chartList}\left(C\right)\right) \leq \operatorname{pow}\left(3, \operatorname{card}\left(\operatorname{Classes}\left(C\right)\right)\right)) \land (\forall theta: \operatorname{Chart}\left(C\right), (\operatorname{member}\left(theta, \operatorname{chartList}\left(C\right)\right))) \land (\forall theta: (\operatorname{Classes}\left(C\right)) \to (\operatorname{Option}\left(Bool\right)), (\operatorname{computedTarget}\left(C, theta\right) = \operatorname{target}\left(C, theta\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.finite_root_minimax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The retained result combines the constant-target or splitting-menu recurrence, attaining tree, all-competitor lower bound, chart length at most 3 raised to the number of occurring classes, exact semantic chart completeness, and computed-target agreement.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.admissibleCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.admissibleCode_spec`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.chartList`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.computedTarget`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.finite_root_minimax`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.minimaxTree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.minimaxValue`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility](NativeFullRootFeasibility.md)
