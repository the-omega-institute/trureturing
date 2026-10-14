# Finite response tables

## Abstract

Finite response tables compute least forgetting depths and deterministic sorted quotient sections for numbered incoming lifts.

Throughout, n and q are arbitrary natural numbers, A is a natural count matrix on Fin n, and L is an IncomingLift A (Fin q), including its given surjective projection and typed numbered-edge lifts. Nat subtraction is truncated. ForgettingDepths(L) denotes every natural d satisfying Forgets(L,d), without a bounded-depth restriction. In the displays, liftValue(L,edge(i,j,a),u) is the value of the typed lift in the guarded target fiber; proof arguments are implicit. sortedIndex and sortedEntry are the inverse and forward maps of the increasing Finset.orderIsoOfFin, and QuotientClass denotes the response class at the displayed depth.

**Definition 1.1 (Numbered input arrays).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \operatorname{Fields}\left(\operatorname{LiftTables}\left(n, q, A\right), \operatorname{project}\left(\operatorname{Fin}\left(q\right) \to \operatorname{Fin}\left(n\right)\right), \operatorname{predecessor}\left(\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), a \in \operatorname{Fin}\left(\operatorname{entry}\left(A, i, j\right)\right), u \in \operatorname{Fin}\left(q\right),\; \operatorname{Fin}\left(q\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.LiftTables` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input stores a projection from Fin q to Fin n and a predecessor state for every ordered pair of base vertices, every parallel edge number and every state. Target-fiber checks precede use of entries.

**Definition 1.2 (Finite input validation).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall T \in \operatorname{LiftTables}\left(n, q, A\right),\; \operatorname{valid}\left(T\right) = \operatorname{decide}\left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \exists u \in \operatorname{Fin}\left(q\right),\; \operatorname{project}\left(T, u\right) = i\right) \land \left(\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), a \in \operatorname{Fin}\left(\operatorname{entry}\left(A, i, j\right)\right), u \in \operatorname{Fin}\left(q\right),\; \operatorname{project}\left(T, u\right) = j \Rightarrow \operatorname{project}\left(T, \operatorname{predecessor}\left(T, i, j, a, u\right)\right) = i\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.valid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean validator checks surjectivity and source-fiber coherence for each actual numbered edge whenever the supplied state lies in its target fiber. Zero edge counts and empty finite domains remain part of the input family.

**Definition 1.3 (Typed incoming lift).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall T \in \operatorname{LiftTables}\left(n, q, A\right), h \in \operatorname{valid}\left(T\right) = \mathit{true},\; \operatorname{project}\left(\operatorname{toLift}\left(T, h\right)\right) = \operatorname{project}\left(T\right) \land \left(\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), a \in \operatorname{Fin}\left(\operatorname{entry}\left(A, i, j\right)\right), u \in \operatorname{Fin}\left(q\right), hu \in \operatorname{project}\left(T, u\right) = j,\; \operatorname{liftValue}\left(\operatorname{toLift}\left(T, h\right), \operatorname{edge}\left(i, j, a\right), u\right) = \operatorname{predecessor}\left(T, i, j, a, u\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.toLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A successful validator supplies the proof fields of the original IncomingLift structure. The projection and predecessor values are the supplied entries themselves.

**Definition 1.4 (Pathwise response table).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right), v \in \operatorname{Fin}\left(q\right),\; \operatorname{table}\left(L, 0, u, v\right) = \operatorname{decide}\left(u = v\right) \land \operatorname{table}\left(L, d + 1, u, v\right) = \operatorname{andBool}\left(\operatorname{decide}\left(\operatorname{project}\left(L, u\right) = \operatorname{project}\left(L, v\right)\right), \operatorname{decide}\left(\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), a \in \operatorname{Fin}\left(\operatorname{entry}\left(A, i, j\right)\right),\; \left(\operatorname{project}\left(L, u\right) = j \land \operatorname{project}\left(L, v\right) = j\right) \Rightarrow \operatorname{table}\left(L, d, \operatorname{liftValue}\left(L, \operatorname{edge}\left(i, j, a\right), u\right), \operatorname{liftValue}\left(L, \operatorname{edge}\left(i, j, a\right), v\right)\right) = \mathit{true}\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Depth zero compares original state numbers. A successor first checks equality of projections, then checks the preceding table on both lifts along each identical numbered incoming edge. Parallel edges are never merged or averaged.

**Definition 1.5 (Whole-fiber forgetting).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \forall d \in \mathit{Nat},\; \operatorname{forgets}\left(L, d\right) = \operatorname{decide}\left(\forall u \in \operatorname{Fin}\left(q\right), v \in \operatorname{Fin}\left(q\right),\; \operatorname{project}\left(L, u\right) = \operatorname{project}\left(L, v\right) \Rightarrow \operatorname{table}\left(L, d, u, v\right) = \mathit{true}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.forgets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a given depth, every pair in each terminal projection fiber must have a true response-table bit. This is a pathwise forgetting test, not a marginal count.

**Definition 1.6 (Inclusive finite depth search).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \forall d \in \mathit{Nat},\; d \in \operatorname{successes}\left(L\right) \Leftrightarrow \left(d \le q - n \land \operatorname{forgets}\left(L, d\right) = \mathit{true}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.successes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The successful-depth set filters every natural number from zero through q minus n, inclusive, using the actual forgetting Boolean.

**Definition 1.7 (Least forgetting decision).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \operatorname{minimumDepth}\left(L\right) = \operatorname{ifThenElse}\left(\operatorname{Nonempty}\left(\operatorname{successes}\left(L\right)\right), \operatorname{some}\left(\operatorname{minimumElement}\left(\operatorname{successes}\left(L\right)\right)\right), \mathit{none}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.minimumDepth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The result is some of the finite set minimum when a successful entry exists, and none otherwise. The implementation uses Finset.min'; the global completeness justification reuses the existing common nilpotency bound.

**Definition 1.8 (Response class enumeration).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right), v \in \operatorname{Fin}\left(q\right),\; v \in \operatorname{members}\left(L, d, u\right) \Leftrightarrow \operatorname{table}\left(L, d, v, u\right) = \mathit{true}$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.members` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a supplied state, the class is the finite set of original state numbers whose table comparison with that state is true.

**Definition 1.9 (Least original state representative).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right),\; \operatorname{representative}\left(L, d, u\right) = \operatorname{minimumElement}\left(\operatorname{members}\left(L, d, u\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.representative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The representative is the least member of that class. The supplied state certifies nonemptiness; no inhabitant of an empty state domain is chosen.

**Definition 1.10 (Sorted representative set).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right),\; u \in \operatorname{representatives}\left(L, d\right) \Leftrightarrow \operatorname{representative}\left(L, d, u\right) = u$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fixed points of the representative operation form the finite set of class representatives, ordered by the original state numbers.

**Definition 1.11 (Dense sorted class numbers).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right),\; \operatorname{classOf}\left(L, d, u\right) = \operatorname{sortedIndex}\left(\operatorname{representatives}\left(L, d\right), \operatorname{representative}\left(L, d, u\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.classOf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse of Finset.orderIsoOfFin maps the computed least representative to its dense finite class index. Numbering follows the sorted state order.

**Definition 1.12 (Computed quotient section).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \forall d \in \mathit{Nat}, i \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{representatives}\left(L, d\right)\right)\right),\; \operatorname{representativeAt}\left(L, d, i\right) = \operatorname{sortedEntry}\left(\operatorname{representatives}\left(L, d\right), i\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.representativeAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward order isomorphism maps a dense class index to its original representative state. Its domain depends on the computed representative count.

**Definition 1.13 (Explicit quotient transport).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \left(\forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right),\; \operatorname{apply}\left(\operatorname{quotientEquiv}\left(L, d\right), \operatorname{QuotientClass}\left(L, d, u\right)\right) = \operatorname{classOf}\left(L, d, u\right)\right) \land \left(\forall d \in \mathit{Nat}, i \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{representatives}\left(L, d\right)\right)\right),\; \operatorname{inverseApply}\left(\operatorname{quotientEquiv}\left(L, d\right), i\right) = \operatorname{QuotientClass}\left(L, d, \operatorname{representativeAt}\left(L, d, i\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.quotientEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Quotient.lift sends a semantic response class to its computed dense index. The inverse uses the computed section. The executable output uses neither Quotient.out nor Fintype.equivFin nor classical witness selection.

**Definition 1.14 (Numbered identity and swap input).**

$$\forall a \in \operatorname{Fin}\left(2\right), u \in \operatorname{Fin}\left(2\right),\; \operatorname{project}\left(\mathit{parallelIdentityFlipTables}, u\right) = 0 \land \operatorname{predecessor}\left(\mathit{parallelIdentityFlipTables}, 0, 0, a, u\right) = \operatorname{ifThenElse}\left(a = 0, u, \operatorname{ifThenElse}\left(u = 0, 1, 0\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.parallelIdentityFlipTables` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This concrete checker input has one base vertex, two states and two parallel edges. Edge number zero preserves the state; edge number one swaps the two states. The bounded checker tests both numbered lifts separately.

**Theorem 1.15 (Complete finite response and quotient refinement).**

$$\forall n \in \mathit{Nat}, q \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right),\; \forall L \in \operatorname{IncomingLift}\left(A, \operatorname{Fin}\left(q\right)\right),\; \left(\forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right), v \in \operatorname{Fin}\left(q\right),\; \operatorname{table}\left(L, d, u, v\right) = \mathit{true} \Leftrightarrow \operatorname{response}\left(L, d, u, v\right)\right) \land \left(\left(\forall d \in \mathit{Nat},\; \operatorname{forgets}\left(L, d\right) = \mathit{true} \Leftrightarrow \operatorname{Forgets}\left(L, d\right)\right) \land \left(\left(\forall d \in \mathit{Nat},\; \operatorname{minimumDepth}\left(L\right) = \operatorname{some}\left(d\right) \Leftrightarrow \operatorname{IsLeast}\left(\operatorname{ForgettingDepths}\left(L\right), d\right)\right) \land \left(\left(\operatorname{minimumDepth}\left(L\right) = \mathit{none} \Leftrightarrow \left(\neg \left(\exists d \in \mathit{Nat},\; \operatorname{Forgets}\left(L, d\right)\right)\right)\right) \land \left(\left(\forall d \in \mathit{Nat},\; \operatorname{minimumDepth}\left(L\right) = \operatorname{some}\left(d\right) \Rightarrow d \le q - n\right) \land \left(\left(\forall d \in \mathit{Nat},\; \operatorname{table}\left(L, d + 1\right) = \operatorname{table}\left(L, d\right) \Rightarrow \left(\forall t \in \mathit{Nat},\; \operatorname{table}\left(L, d + t\right) = \operatorname{table}\left(L, d\right)\right)\right) \land \left(\left(\forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right), v \in \operatorname{Fin}\left(q\right),\; \operatorname{classOf}\left(L, d, u\right) = \operatorname{classOf}\left(L, d, v\right) \Leftrightarrow \operatorname{response}\left(L, d, u, v\right)\right) \land \left(\left(\forall d \in \mathit{Nat}, i \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{representatives}\left(L, d\right)\right)\right),\; \operatorname{classOf}\left(L, d, \operatorname{representativeAt}\left(L, d, i\right)\right) = i\right) \land \left(\left(\forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right),\; \operatorname{representativeAt}\left(L, d, \operatorname{classOf}\left(L, d, u\right)\right) = \operatorname{representative}\left(L, d, u\right)\right) \land \left(\left(\forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right),\; \operatorname{response}\left(L, d, \operatorname{representative}\left(L, d, u\right), u\right)\right) \land \left(\forall d \in \mathit{Nat}, u \in \operatorname{Fin}\left(q\right), v \in \operatorname{Fin}\left(q\right),\; \operatorname{response}\left(L, d, v, u\right) \Rightarrow \operatorname{representative}\left(L, d, u\right) \le v\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.finite_response_table_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

1. For every depth and every pair of states, the table bit is true exactly when the original IncomingLift response relation holds.

2. For every depth, the whole-fiber forgetting Boolean is true exactly when the original Forgets predicate holds.

3. For every natural depth, minimumDepth returns that depth exactly when it is least among all forgetting depths.

4. minimumDepth is none exactly when no finite forgetting depth exists.

5. Every returned depth is at most q minus n, with truncated natural subtraction and no added bound hypothesis.

6. Equality of two adjacent whole response tables persists at every later depth.

7. Two dense class numbers agree exactly when their states have the original response relation.

8. Classifying the selected state of any dense class returns the same class index.

9. Selecting the class of a state returns its computed least representative.

10. Every computed representative is response-related to its input state.

11. That representative is no greater than any response-related original state number.

The proof relates the actual edge recursion to response_successor_iff and response_zero_and_step, connects forgetting to the private original pathwise kernel equivalence, and uses the existing common_nilpotency_forgetting_bound. The new algorithm refinement is distinct from those supplier results.

The theorem concerns one incoming lift. Separate applications can supply independent least depths for two lifts, but this module does not construct a controlled trace, serialize a trace exporter or decide a fixed-positive-lag certificate.

The domain permits zero states, zero base vertices, zero edge counts and depth zero. Surjectivity is part of the supplied IncomingLift. No essentiality, positive order, common lag, certificate or extra finite bound is added to this one-lift result.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.LiftTables`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.classOf`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.finite_response_table_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.forgets`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.members`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.minimumDepth`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.parallelIdentityFlipTables`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.quotientEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.representative`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.representativeAt`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.representatives`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.successes`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.table`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.toLift`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteResponseTable.valid`
- Dependency: [D5/S3/ConceptDynamics/Coding/CommonNilpotencyForgettingBound](CommonNilpotencyForgettingBound.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseKernelRecursion](ResponseKernelRecursion.md)
