# Exact positive-drift completed region split

## Abstract

CompletionPositiveDriftRegion

**Theorem 1.1 (A positive cycle forces its whole forward region to be atomic or leafless).**

$$\forall k, m: Nat, (\forall E: \operatorname{System}\left(k, m\right), (\forall mode: (\operatorname{Fin}\left(k\right)) \to (Bool), (\forall param: (\operatorname{Fin}\left(k\right)) \to (Nat), (\forall root: \operatorname{Fin}\left(m\right), (\forall c: \operatorname{PositiveCycle}\left(E, root\right), (\forall extra: ((\operatorname{Fin}\left(m\right)) \to (\operatorname{CompletionTree}\left(\right))) \to (Prop), (\forall v: (\operatorname{Fin}\left(m\right)) \to (\operatorname{CompletionTree}\left(\right)), (((\operatorname{Solution}\left(E, mode, param, extra, v\right)) \iff ((\operatorname{FiniteAlternative}\left(c, mode, param, extra, v\right)) \lor (\operatorname{InfiniteAlternative}\left(c, mode, param, extra, v\right)))) \land (\neg ((\operatorname{FiniteAlternative}\left(c, mode, param, extra, v\right)) \land (\operatorname{InfiniteAlternative}\left(c, mode, param, extra, v\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/CompletionPositiveDriftRegion.positive_drift_region_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The system E is any finite list of positive equalities between normalized expressions in finite grounds, scalar tokens, decorated residuals and ordered pairs. A Boolean scalar mode chooses finite atomic tokens with natural parameters and nonnegative offsets or the leafless tree Omega. Repeated names share one valuation. Exposed equations include both orientations and pair cancellation, so all occurrences from all exposed definitions contribute edges.

A PositiveCycle is a closed walk with a nonempty occurrence address on at least one edge and a strictly positive sum of integer head-power minus occurrence-power differences. The result therefore includes every simple cycle with these properties. Region is forward reachability from every cycle vertex in the entire exposed graph; it does not include incoming predecessors solely because they point into the region.

FiniteAlternative assigns a unique natural rank to each region coordinate and replaces that coordinate by the corresponding atomic tree. InfiniteAlternative replaces every region coordinate by Omega. Both replacements leave every outside coordinate equal to its original value. Each alternative includes the reconstruction equality and the complete Solution predicate: every original equation and the arbitrary extra predicate must still hold. No branch is assumed satisfiable, and restrictions on the natural ranks arise only from these retained obligations.

The finite argument propagates finiteness and nonincreasing native mass along occurrence edges. Strict decrease of positive mass on a strict edge forces cycle mass, and then every forward mass, to vanish. Zero mass characterizes the atomic orbit, whose injective rank gives uniqueness. The infinite argument uses infinite_subtree_origin to recover an actual subtree of the same original head tree. Along a walk, the concatenated address and cumulative powers satisfy one transport identity. Repeating the positive cycle gives arbitrarily deep native preimages; full prefixes force the root to be Omega, and occurrence edges propagate Omega throughout the region.

The displayed equivalence proves both directions, and the second conjunct proves disjointness. The extra predicate may retain scalar guards, reconstruction constraints, mixed completed comparisons and predicates with captured finite-source chart parameters in their original types. This is a symbolic classification on unrestricted completed trees, not a bounded enumeration or a numerical certificate. It does not assert an expression-normalization algorithm, a cycle-search algorithm, a Presburger compiler, or a solver for arbitrary systems. The result is derived within the repository's native substitution theory; no external novelty is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CompletionPositiveDriftRegion.positive_drift_region_split`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CompletionHomogeneousFixedPoints](CompletionHomogeneousFixedPoints.md)
