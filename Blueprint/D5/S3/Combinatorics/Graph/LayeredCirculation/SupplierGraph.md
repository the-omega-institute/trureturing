# SupplierGraph

## Abstract

The necessary finite typed-walk and real flow interface is a licensed source transplant from elazarg/multitubes at commit 20d22aa7ca67f9843e5adf9edf173403a2f4033a. The original proof source is identified in the Lean license notice. These helpers are consumed by the real layered local-law theorem; no new mathematical novelty is attributed to the supplier.

Generic declarations use these source contexts: universe uV uE variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E) variable {G} {start finish middle : V} universe uV uE variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E) variable {G} {start finish : V} universe uV uE variable {V : Type uV} {E : Type uE} {G : Maths.EdgeGraph V E} {start finish : V}

**Definition 1.1 (length).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] def length {start : V} : {finish : V} → G.Walk start finish → ℕ | _, .nil => 0 | _, .concat walkSoFar _ _ => walkSoFar.length + 1

**Definition 1.2 (edges).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def edges {start : V} : {finish : V} → G.Walk start finish → List E | _, .nil => [] | _, .concat walkSoFar edge _ => walkSoFar.edges ++ [edge]

**Theorem 1.3 (length concat).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_concat`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_concat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem length_concat (walkSoFar : G.Walk start finish) (edge : E) (legal : G.source edge = finish) : (Walk.concat walkSoFar edge legal).length = walkSoFar.length + 1

**Theorem 1.4 (edges concat).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_concat`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_concat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem edges_concat (walkSoFar : G.Walk start finish) (edge : E) (legal : G.source edge = finish) : (Walk.concat walkSoFar edge legal).edges = walkSoFar.edges ++ [edge]

**Theorem 1.5 (edges length).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_length`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem edges_length (walk : G.Walk start finish) : walk.edges.length = walk.length

**Definition 1.6 (visited).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.visited`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.visited` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def visited {start : V} : {finish : V} → G.Walk start finish → List V | _, .nil => [start] | _, .concat walkSoFar edge _ => walkSoFar.visited ++ [G.target edge]

**Theorem 1.7 (length visited).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_visited`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_visited` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem length_visited (walk : G.Walk start finish) : walk.visited.length = walk.length + 1

**Theorem 1.8 (mem visited of mem edges).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.mem_visited_of_mem_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.mem_visited_of_mem_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem mem_visited_of_mem_edges (walk : G.Walk start finish) {edge : E} (hmem : edge ∈ walk.edges) : G.target edge ∈ walk.visited

**Theorem 1.9 (edges nodup of visited nodup).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_nodup_of_visited_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_nodup_of_visited_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem edges_nodup_of_visited_nodup (walk : G.Walk start finish) (hnd : walk.visited.Nodup) : walk.edges.Nodup

**Theorem 1.10 (exists split of mem visited).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_split_of_mem_visited`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_split_of_mem_visited` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem exists_split_of_mem_visited (walk : G.Walk start finish) {vertex : V} (hmem : vertex ∈ walk.visited) : ∃ (before : G.Walk start vertex) (after : G.Walk vertex finish), walk.edges = before.edges ++ after.edges

**Theorem 1.11 (exists closedSubwalk of not nodup).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_closedSubwalk_of_not_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_closedSubwalk_of_not_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem exists_closedSubwalk_of_not_nodup (walk : G.Walk start finish) (hdup : ¬ walk.visited.Nodup) : ∃ (vertex : V) (before : G.Walk start vertex) (cycle : G.Walk vertex vertex) (after : G.Walk vertex finish), 0 < cycle.length ∧ walk.edges = before.edges ++ cycle.edges ++ after.edges

**Theorem 1.12 (edges isChain).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_isChain`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_isChain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem edges_isChain (walk : G.Walk start finish) : walk.edges.IsChain fun first second => G.target first = G.source second

**Theorem 1.13 (source head).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.source_head`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.source_head` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem source_head (walk : G.Walk start finish) (hne : walk.edges ≠ []) : G.source (walk.edges.head hne) = start

**Theorem 1.14 (target getLast).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.target_getLast`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.target_getLast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem target_getLast (walk : G.Walk start finish) (hne : walk.edges ≠ []) : G.target (walk.edges.getLast hne) = finish

**Definition 1.15 (edgeMultiplicity).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] def edgeMultiplicity [DecidableEq E] {start : V} : {finish : V} → G.Walk start finish → E → ℕ | _, .nil => fun _ => 0 | _, .concat walkSoFar edge _ => fun candidate => walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0

**Theorem 1.16 (edgeMultiplicity pos iff mem edges).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_pos_iff_mem_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_pos_iff_mem_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem edgeMultiplicity_pos_iff_mem_edges [DecidableEq E] (walk : G.Walk start finish) (edge : E) : 0 < walk.edgeMultiplicity edge ↔ edge ∈ walk.edges

**Theorem 1.17 (edgeMultiplicity eq count).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_eq_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_eq_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem edgeMultiplicity_eq_count [DecidableEq E] (walk : G.Walk start finish) (edge : E) : walk.edgeMultiplicity edge = walk.edges.count edge

**Theorem 1.18 (edgeMultiplicity eq one iff mem edges).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_eq_one_iff_mem_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_eq_one_iff_mem_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem edgeMultiplicity_eq_one_iff_mem_edges [DecidableEq E] (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) : walk.edgeMultiplicity edge = 1 ↔ edge ∈ walk.edges

**Definition 1.19 (castFinish).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.castFinish`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.castFinish` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def castFinish {start finish finish' : V} (walk : G.Walk start finish) (hfinish : finish = finish') : G.Walk start finish' := hfinish ▸ walk

**Theorem 1.20 (length castFinish).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_castFinish`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_castFinish` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem length_castFinish {start finish finish' : V} (walk : G.Walk start finish) (hfinish : finish = finish') : (walk.castFinish hfinish).length = walk.length

**Theorem 1.21 (edges castFinish).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_castFinish`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_castFinish` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem edges_castFinish {start finish finish' : V} (walk : G.Walk start finish) (hfinish : finish = finish') : (walk.castFinish hfinish).edges = walk.edges

**Definition 1.22 (castStart).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.castStart`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.castStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def castStart {start start' finish : V} (walk : G.Walk start finish) (hstart : start = start') : G.Walk start' finish := hstart ▸ walk

**Theorem 1.23 (length castStart).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_castStart`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_castStart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem length_castStart {start start' finish : V} (walk : G.Walk start finish) (hstart : start = start') : (walk.castStart hstart).length = walk.length

**Theorem 1.24 (edges castStart).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_castStart`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_castStart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem edges_castStart {start start' finish : V} (walk : G.Walk start finish) (hstart : start = start') : (walk.castStart hstart).edges = walk.edges

**Definition 1.25 (append).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.append`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.append` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] def append {start middle : V} (first : G.Walk start middle) : {finish : V} → G.Walk middle finish → G.Walk start finish | _, .nil => first | _, .concat second edge legal => .concat (first.append second) edge legal

**Theorem 1.26 (edges append).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem edges_append (first : G.Walk start middle) (second : G.Walk middle finish) : (first.append second).edges = first.edges ++ second.edges

**Theorem 1.27 (length append).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem length_append (first : G.Walk start middle) (second : G.Walk middle finish) : (first.append second).length = first.length + second.length

**Definition 1.28 (outgoingMultiplicity).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.outgoingMultiplicity`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.outgoingMultiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def outgoingMultiplicity [Fintype E] [DecidableEq V] (multiplicity : E → ℕ) (vertex : V) : ℕ := ∑ edge with G.source edge = vertex, multiplicity edge

**Definition 1.29 (incomingMultiplicity).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.incomingMultiplicity`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.incomingMultiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def incomingMultiplicity [Fintype E] [DecidableEq V] (multiplicity : E → ℕ) (vertex : V) : ℕ := ∑ edge with G.target edge = vertex, multiplicity edge

**Theorem 1.30 (edgeMultiplicity balanced).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_balanced`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_balanced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem edgeMultiplicity_balanced [Fintype E] [DecidableEq E] [DecidableEq V] {base : V} (walk : G.Walk base base) (vertex : V) : G.outgoingMultiplicity walk.edgeMultiplicity vertex = G.incomingMultiplicity walk.edgeMultiplicity vertex

**Definition 1.31 (singleton).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.singleton`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.singleton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def singleton (edge : E) : G.Walk (G.source edge) (G.target edge) := .concat .nil edge rfl

**Theorem 1.32 (exists splitAtEdge).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_splitAtEdge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_splitAtEdge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem exists_splitAtEdge (walk : G.Walk start finish) (edge : E) (hmem : edge ∈ walk.edges) : ∃ (before : G.Walk start (G.source edge)) (after : G.Walk (G.target edge) finish), walk.edges = before.edges ++ edge :: after.edges

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.append`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.castFinish`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.castStart`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_balanced`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_eq_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_eq_one_iff_mem_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_pos_iff_mem_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_append`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_castFinish`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_castStart`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_concat`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_isChain`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_length`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_nodup_of_visited_nodup`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_closedSubwalk_of_not_nodup`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_splitAtEdge`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_split_of_mem_visited`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.incomingMultiplicity`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_append`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_castFinish`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_castStart`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_concat`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_visited`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.mem_visited_of_mem_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.outgoingMultiplicity`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.singleton`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.source_head`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.target_getLast`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.visited`
