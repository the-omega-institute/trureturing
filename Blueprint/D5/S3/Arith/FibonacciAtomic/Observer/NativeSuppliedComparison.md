# Fixed skeleton query separation

## Abstract

NativeSuppliedComparison

Fix one public full ordered skeleton S. Its chart numbers every original leaf once, in order, and its address map retains the actual depth of each leaf. The source u(S,x) fills that same chart with alpha for false and beta for true. Correct(M,S,T) quantifies every independent assignment x and every entry t from zero through T. For each there is a finite first-halt Run, and every such Run outputs the original XOR. Static(M,S,T) says that every promised Run has zero genuine Updates. Neither predicate supplies the actual lag to the controller, imposes a common runtime, or excludes unreachable Update rows.

The controller's entire mutable state is its state word. A state selects one fixed literal or a source-blind internal instruction, a genuine Update with constant acknowledgement, or a fixed-output halt. Run retains the query state together with its absolute actual epoch. The replay theorem compares the same evolving original sources at those epochs, retaining arbitrary finite internal work. The installed query and halt sets count every state of their respective instruction types, whether or not a promised source reaches it.

**Theorem 1.1 (Distinct words on each actual run).**

$$\forall E: Type, (\forall M: \operatorname{Controller}\left(E\right), (\forall S: Source, (\forall T: Nat, (\forall x: \operatorname{Fin}\left(\operatorname{length}\left(S\right)\right) \to Bool, (\forall t: Nat, (\forall q: \operatorname{List}\left(\operatorname{Product}\left(E, Nat\right)\right), (\forall u: Nat, (\forall f: E, (\forall b: Bool, ((\operatorname{Correct}\left(M, S, T\right)) \implies ((t \leq T) \implies ((\operatorname{Run}\left(M, \operatorname{source}\left(\operatorname{chartOf}\left(S\right), x\right), \operatorname{initial}\left(M\right), t, q, u, f, b\right)) \implies (\exists p: \operatorname{Fin}\left(\operatorname{length}\left(S\right)\right) \to E, ((\operatorname{Injective}\left(p\right)) \land (\forall i: \operatorname{Fin}\left(\operatorname{length}\left(S\right)\right), (\exists n: Nat, ((\operatorname{pair}\left(\operatorname{p}\left(i\right), n\right) \in q) \land ((\operatorname{IsPrefix}\left(\operatorname{address}\left(\operatorname{chartOf}\left(S\right), i\right), \operatorname{literal}\left(M, \operatorname{p}\left(i\right)\right)\right)) \land (\operatorname{readout}\left(\operatorname{literal}\left(M, \operatorname{p}\left(i\right)\right), \operatorname{iterate}\left(n, \operatorname{source}\left(\operatorname{chartOf}\left(S\right), x\right)\right)\right) \neq \operatorname{readout}\left(\operatorname{literal}\left(M, \operatorname{p}\left(i\right)\right), \operatorname{iterate}\left(n, \operatorname{source}\left(\operatorname{chartOf}\left(S\right), \operatorname{flip}\left(x, i\right)\right)\right)\right))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison.same_run_distinct_queries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coordinate is compared with its one-label flip in the identical original chart at the identical entry. If all Read replies on the chosen run agreed, exact replay would give the same fixed halt on opposite original parities. A literal can depend only on the unique original leaf cone it enters; a literal ending inside the skeleton has no label dependence. Numbered-row locality includes absent replies. Pairwise prefix disjointness of the original cones therefore makes the chosen query states injective, even when a query state recurs at a different source epoch.

**Theorem 1.2 (All installed states).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Controller}\left(E\right), (\forall S: Source, (\forall T: Nat, ((\operatorname{Correct}\left(M, S, T\right)) \implies ((\operatorname{length}\left(S\right) \leq \operatorname{card}\left(\operatorname{queries}\left(M\right)\right)) \land ((2 \leq \operatorname{card}\left(\operatorname{halts}\left(M\right)\right)) \land ((\operatorname{length}\left(S\right)) + (2) \leq \operatorname{card}\left(E\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison.installed_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are at least h query states, where h is the leaf count of S. Both original XOR values occur across the full assignment family, so two distinct fixed-output halt states are installed. The query and halt sets are disjoint. The two halts occur across assignments; they are not asserted to occur on one run.

**Theorem 1.3 (Static entry cover).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Controller}\left(E\right), (\forall S: Source, (\forall T: Nat, ((\operatorname{Correct}\left(M, S, T\right)) \implies ((\operatorname{Static}\left(M, S, T\right)) \implies (((\operatorname{length}\left(S\right))(\operatorname{div}\left((T) + (3), 3\right)) \leq \operatorname{card}\left(\operatorname{queries}\left(M\right)\right)) \land (((\operatorname{length}\left(S\right))(\operatorname{div}\left((T) + (3), 3\right))) + (2) \leq \operatorname{card}\left(E\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison.static_installed_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each original index and each t from zero through T, compare the all-zero assignment with its single-coordinate flip. Every separating query has actual epoch t, because that promised run has zero Updates. Removing that leaf's own address leaves a suffix separating atomic ranks t and t plus one. The guarded atomic window places these entries among at most three consecutive ranks for a fixed suffix. Encoding an entry by its selected query and one of three offsets proves that the cone has at least r=(T+3)/3 query states. Summing over disjoint original cones gives h times r query states and two additional halts. This is a union of installed words over entries, with no assertion of h times r Reads on one run.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison.installed_lower_bound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison.same_run_distinct_queries`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison.static_installed_lower_bound`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CombLiteralInstallationBounds](CombLiteralInstallationBounds.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFibonacciStaticScan](NativeFibonacciStaticScan.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound](SparseLiteralParityReadLowerBound.md)
