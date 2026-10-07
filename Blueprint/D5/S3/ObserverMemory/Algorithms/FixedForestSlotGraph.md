# Shared rows and directed edge multiplicity

## Abstract

Complete-history incidence gives the exact original directed slot statistics.

The slot of a history is its assigned read target and absolute digit. A nonroot history indexes the directed edge from its unique parent's slot. Incoming degree counts distinct source rows, while edge multiplicity counts complete-history preimages. Multiple input visits do not add edge preimages. The two shared rows are w={H,K} and v={H1,K1}; they are distinct. Read-control cycles and the allowed T=Q case remain unrestricted.

**Theorem 1.1 (Full nonroot history accounting).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall S:Type,{\forall eqS:\operatorname {DecidableEq}(S),{\forall row:\operatorname {Function}(Node,S),{\operatorname {historySurplus}(F,row)=\operatorname {rawJ}(F,row)+\operatorname {rawXi}(F,row)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.raw_history_surplus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partition nonroot histories by directed edge and partition distinct edges by their target row. The sum of fiber cardinal minus one equals domain cardinal minus image cardinal. The resulting identity uses complete histories and has no graph acyclicity premise.

**Theorem 1.2 (Exact row-image transport).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall S:Type,{\forall eqS:\operatorname {DecidableEq}(S),{\forall T:Type,{\forall eqT:\operatorname {DecidableEq}(T),{\forall row:\operatorname {Function}(Node,S),{\forall f:\operatorname {Function}(S,T),{\operatorname {rawRows}(F,\operatorname {compose}(f,row))=\operatorname {image}(f,\operatorname {rawRows}(F,row))}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawRows_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changing the row carrier maps precisely the nonroot history row image. No surjectivity is needed.

**Theorem 1.3 (Exact edge-image transport).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall S:Type,{\forall eqS:\operatorname {DecidableEq}(S),{\forall T:Type,{\forall eqT:\operatorname {DecidableEq}(T),{\forall row:\operatorname {Function}(Node,S),{\forall f:\operatorname {Function}(S,T),{\operatorname {rawEdges}(F,\operatorname {compose}(f,row))=\operatorname {image}(\operatorname {productMap}(f,f),\operatorname {rawEdges}(F,row))}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawEdges_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both endpoints of every original history edge are mapped, with the same finite nonroot domain.

**Theorem 1.4 (Incoming-degree transport).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall S:Type,{\forall eqS:\operatorname {DecidableEq}(S),{\forall T:Type,{\forall eqT:\operatorname {DecidableEq}(T),{\forall row:\operatorname {Function}(Node,S),{\forall f:\operatorname {Function}(S,T),{{\operatorname {Injective}(f)}\implies{\operatorname {rawJ}(F,\operatorname {compose}(f,row))=\operatorname {rawJ}(F,row)}}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawJ_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity preserves each incoming-edge fiber under the product map. Its image cardinal is unchanged, and summing over the exact row image preserves the indegree surplus.

**Theorem 1.5 (History edge-fiber transport).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall S:Type,{\forall eqS:\operatorname {DecidableEq}(S),{\forall T:Type,{\forall eqT:\operatorname {DecidableEq}(T),{\forall row:\operatorname {Function}(Node,S),{\forall f:\operatorname {Function}(S,T),{{\operatorname {Injective}(f)}\implies{\operatorname {rawXi}(F,\operatorname {compose}(f,row))=\operatorname {rawXi}(F,row)}}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawXi_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonroot histories mapping to an injected edge are exactly the original edge fiber. Their cardinalities and the sum over the finite edge image remain equal.

**Theorem 1.6 (Canonical and raw incoming statistics agree).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{\operatorname {rawJ}(F,\operatorname {placement}(F,R,alpha))=\operatorname {J}(F,R,alpha)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawJ_placement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Edges ending at a row are in bijection with its distinct predecessor rows. Rows outside the nonroot image have no incoming edges and contribute zero.

**Theorem 1.7 (Canonical and raw repetition statistics agree).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{\operatorname {rawXi}(F,\operatorname {placement}(F,R,alpha))=\operatorname {Xi}(F,R,alpha)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawXi_placement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical edge preimage is exactly the raw nonroot history fiber. Edges outside the finite edge image have empty fibers and contribute zero.

**Theorem 1.8 (The prescribed double rows differ).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\operatorname {placement}(F,R,alpha,\operatorname {H}(R))\neq\operatorname {placement}(F,R,alpha,\operatorname {H1}(R))}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.shared_rows_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compatibility and the four distinct marked nodes exclude equality of the two prescribed rows.

**Theorem 1.9 (The original surpluses exclude every additional collision).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{\forall S:Type,{\forall eqS:\operatorname {DecidableEq}(S),{\forall row:\operatorname {Function}(Node,S),{\forall n:Node,{\forall m:Node,{{\operatorname {prescribedRawHypotheses}(F,R,row,n,m)}\implies{\operatorname {Shared}(F,R,n,m)}}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.raw_fibers_only` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any row carrier with decidable equality, the H/K and H1/K1 pairs occupy distinct rows. If rawJ=rawXi=1, their two fiber excesses exhaust the total. Every nonroot equal-row pair is therefore exactly one of the prescribed pairs, or an identical node. The hypotheses are row(H)=row(K), row(H1)=row(K1), row(H) unequal row(H1), rawJ=rawXi=1, nonroot n and m, and row(n)=row(m).

**Theorem 1.10 (The sole repeated edge).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\forall n:Node,{\forall m:Node,{{\operatorname {sameNonrootEdge}(F,R,alpha,n,m)}\implies{\operatorname {equalOrResolvingPair}(R,n,m)}}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.repeated_edge_only` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal directed edges with distinct forest preimages can only be H1/K1. H/K have distinct binary source rows; H1/K1 have the same source row w and target row v.

**Theorem 1.11 (J equals one).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\operatorname {J}(F,R,alpha)=1}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.incoming_excess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only w has two incoming source rows. Every other used row has at most one; roots and unused rows contribute zero to the sum of incoming degree minus one.

**Theorem 1.12 (Xi equals one).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\operatorname {Xi}(F,R,alpha)=1}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.repetition_excess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The edge w to v has exactly two complete-history preimages. Every other edge has at most one.

**Theorem 1.13 (Binary sharing equals one).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{\operatorname {sharing}(F,R,alpha)=1}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.sharing_excess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A/B are the only merged binary target. All other binary parents represent separate targets. This counts histories and also covers H=A or H=B.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.incoming_excess`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawEdges_map`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawJ_map`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawJ_placement`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawRows_map`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawXi_map`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.rawXi_placement`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.raw_fibers_only`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.raw_history_surplus`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.repeated_edge_only`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.repetition_excess`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.shared_rows_distinct`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph.sharing_excess`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory](FixedForestTargetInventory.md)
