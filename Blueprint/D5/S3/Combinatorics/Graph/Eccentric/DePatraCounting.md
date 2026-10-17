# Native Bridge and Pendant Counting

## Abstract

Actual connected vertex-and-edge subgraphs give the bridge and pendant counting identities. Every non-endpoint eccentricity strictly increases under the bridge shift, including comparison against the fresh-leaf target.

These are independently proved counting ingredients for Conjecture 2.9 of Akash De and Kamal Lochan Patra, On the sum of eccentric subgraph numbers of the vertices of a connected graph, arXiv:2610.19694v1, https://arxiv.org/html/2610.19694v1. All subgraphs are native SimpleGraph.Subgraph values, retaining their vertex sets and independently chosen edge sets. Singletons and non-induced connected subgraphs are included.

**Theorem 1.1 (Separate the singleton pendant vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.pendantRootEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.pendantRootEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose l is outside a side S, r belongs to S, l is adjacent to r, l has no other neighbor in the extended side, and only r can be an exit from S. Connected subgraphs supported in insert(l,S) and containing l are in bijection with Unit plus the connected subgraphs supported in S and containing r. The Unit case is the singleton l. In every other case a path from l to another vertex forces the edge lr. Restriction removes l and that edge; union with the one-edge subgraph reconstructs every selected vertex and edge.

**Theorem 1.2 (A target on the base side forces the pendant edge).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.pendantTargetsEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.pendantTargetsEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonempty target set s contained in S, connected subgraphs supported in insert(l,S) containing l and s correspond bijectively to rooted connected subgraphs on S containing r and s. The singleton l cannot occur because a vertex of s lies in S. The restriction and reconstruction are exact on edges.

**Theorem 1.3 (Two choices at the base root).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.pendant_base_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.pendant_base_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For targets s contained in S, the rooted count at r in the pendant extension equals twice the rooted count on S. Partition by whether l is present. Omitting l leaves precisely a subgraph on S, while including l forces its unique edge and is in bijection with the same rooted choices on S.

**Theorem 1.4 (Supported subgraphs and induced ambient graphs).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.withinInduceEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.withinInduceEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For targets s contained in a side S, connected subgraphs of G supported in S correspond bijectively to connected subgraphs of the ambient induced graph G.induce(S) containing the corresponding targets. This does not require the subgraphs themselves to be induced. Mapping and pulling back preserve connectivity, vertex choices, and every independently selected edge.

**Theorem 1.5 (Positive attained local minima).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.local_root_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.local_root_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the induced graph on S is finite and connected, r belongs to S, and a non-root vertex exists, there is a positive minimum p of the local rooted pair counts to non-root vertices. This minimum is attained, is strictly below the rooted count a, and a is at least two. Transport to the native induced graph applies the singleton-exclusion and attainment results.

**Theorem 1.6 (Same-side counts before contraction).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.bridge_same_side_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.bridge_same_side_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write A and B for the two actual deletion components rooted at u and v, and b for the rooted count on B. For any nonempty target set s in A, let L be the number of local rootless subgraphs containing s and Q the number of local rooted ones containing s. The count in G is L+(1+b)Q. The extended second side is a pendant extension of B and has rooted count 1+b at u, including the singleton u.

**Theorem 1.7 (Same-side counts after contraction).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_same_side_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_same_side_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the same actual targets and local counts, the shifted graph has count L+2bQ. Its first component retains exactly its original adjacency. On the extended second side the shift is the original graph with u and v swapped. At the base root of this pendant side there are two edge-preserving choices for each rooted subgraph of B.

**Theorem 1.8 (Cross-bridge product).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.bridge_pair_cross`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.bridge_pair_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x in A and y in B, the original pair count is the product of the local rooted pair counts from u to x and from v to y. Connectivity forces the exit root, and the rooted gluing and pendant bijections prove the formula for actual subgraphs, without a counting-identity assumption.

**Theorem 1.9 (Cross-component counts after contraction).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_pair_cross`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_pair_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x in A and y in B different from v, the shifted pair count is twice the product of those same local rooted pair counts. The factor two is the independent choice of whether to include the new pendant edge.

**Theorem 1.10 (The fresh leaf has one pendant-edge choice).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_pair_leaf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_pair_leaf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x in A, the shifted pair count to the fresh leaf v is the local rooted pair count from u to x times the rooted count b on B. The new pendant edge is forced, so no factor two appears. The formula includes x=u.

**Theorem 1.11 (Every possible target is checked).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_left_all_targets`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_left_all_targets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x in A different from u, the old eccentricity is strictly below every shifted pair count from x. A target in A uses the increase from L+(1+b)Q to L+2bQ, with Q positive and b at least two. A non-root target in B uses the doubled positive product. For the fresh-leaf target, choose a non-root vertex of B attaining q<b: its old pair count is Uq, strictly below the shifted leaf count Ub. Self and the identified root are included in the first case.

**Theorem 1.12 (All non-endpoint eccentricities improve).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_nonendpoint_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_nonendpoint_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every qualifying bridge and every vertex different from both endpoints, the old eccentricity is strictly smaller than the shifted eccentricity. Choose an attained minimizing target in the shifted graph. The first-side all-target result applies directly, and swapping endpoint names transports the same result to the second component.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.bridge_pair_cross`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.bridge_same_side_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.local_root_minimum`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.pendantRootEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.pendantTargetsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.pendant_base_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_left_all_targets`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_nonendpoint_strict`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_pair_cross`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_pair_leaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.shift_same_side_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting.withinInduceEquiv`
- Dependency: [D5/S3/Combinatorics/Graph/Eccentric/DePatraBridge](DePatraBridge.md)
