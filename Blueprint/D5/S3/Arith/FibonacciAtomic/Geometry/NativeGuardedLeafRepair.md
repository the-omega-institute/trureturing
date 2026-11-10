# Native guarded leaf repair frontiers

## Abstract

Exact guarded original-leaf repair frontiers for actual material trees.

**Theorem 1.1 (Exact F/R cost frontiers).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A source term is the repository's ordered Bool free magma. Material cells are the actual address roster, including retained beta markers, and adjacency is the native parent-child graph. A successful history is a finite list of guarded promote and split calls; its trace is the actual subtree replacement computation and its final domain is the original D predicate. Cost counts successful promotions first and splits second. Minimality is componentwise undominated cost, over every finite successful history at every depth.

The exact undominated cost sets are alpha/F = {(1,0)}, alpha/R = {(0,0)}, beta/F = {(0,0)} and beta/R = {(1,1)}.

F is an actual perfect matching of every material cell. R is an actual matching of every nonroot material cell while the existing root remains present and unmatched. Each promote adds one material cell and each split adds two, so the history cardinality identity gives the promotion parity lower bound. The beta right-rootless lower bound also uses the actual rootless cardinality and the guarded fact that no promotion can precede the first root split.

The four witnesses are the empty alpha and beta histories, one root promotion from alpha, and the legal beta sequence split-at-root followed by promotion at the right child. Their matching edges are constructed on the actual address graph. Material addresses from the original term persist through every successful replacement; zero extension preserves every old rational value and assigns zero to fresh addresses.

Every history lifts to an arbitrary native context by prefixing its actual call addresses with the hole address. The source replacement identity gives its literal final context. The ambient neighbor relation at the prefixed addresses agrees with the local cone graph, so its perfect and root-available matchings transport to the actual cone. Guarded growth preserves D, old material addresses and the induced old edges; those unchanged addresses retain their root depths. The native execution carries arbitrary rational values through each zero extension, moves an alpha's raw binding to its new marker, and on a split moves the old beta-terminal binding to the new left marker while assigning the next raw integer to the right alpha. These computations presume the originally earned raw/canonical correspondence and do not acquire it.

This result concerns only the four leaf frontiers and their source specific witnesses and lower bounds. It does not settle the global recursive frontier, rational determinant claims, acquisition, field operations, storage, traffic, or joint resource optima.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation](../ActualImageAlphaSeparation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition](NativeMaterialRootRecognition.md)
