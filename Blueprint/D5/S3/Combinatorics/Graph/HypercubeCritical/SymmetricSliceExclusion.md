# Symmetric Slice Exclusion

## Abstract

Symmetric Slice Exclusion

Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), ask whether f2(Q9) is three or four. The external problem and its published results belong to that paper. This repository proof addresses a local structural branch; no solution of the original 258-point problem or literature priority is claimed. The original problem remains unresolved.

The original eleven/eleven side counts, four degree-two vertices per side, degrees two or three, independent degree-two vertices and girth at least eight exclude an induced realization in every finite Boolean cube. Derive the actual high-side profiles and discharge all A/A, A/B, B/A and B/B cases. No cycle, high-profile, label-classification or saturation assumption is added to the public claim.

Lean kernel checking supplies the mathematical evidence. Classical label choices and quotient/propositional reasoning use the standard axioms only. The imported finite checks use decide +kernel or ordinary finite case analysis; no SAT result, oracle answer, native_decide or problem-specific axiom is a proof premise.

**Definition 1.1 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closed proposition asserts that there exist n : Nat, a finite subset S of Fin n -> Bool, and two finite sides L,R of its actual induced graph G, such that G is bipartite with those sides, every degree is two or three, no edge joins degree-two vertices, girth is at least eight, both side cardinalities are eleven, and both degree-two side counts are four. Dimension is unrestricted, including zero. Positive degrees force the two sides to cover the vertex set, so their counts give twenty-two actual vertices. No supplied profile, cycle, saturation, label table, graph enumeration or external certificate is a premise.

**Theorem 1.2 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem has literally type Not claim. Classify the actual high graph into side profiles A=(1,6,0) or B=(2,4,1). A/A forces an isolated high edge and a high C12, where actual incidence capacity contradicts eight lows. A/B and B/A force a closed Y and a disjoint actual C8, whose low exhaustion and antipodal leaf neighbors force a genuine forbidden short cycle. B/B forces the explicit twenty-two-point graph, preserves every edge and reflects adjacency by saturated degrees, and contradicts its induced-cube nonembedding theorem. Only B/B needs the cube premise. The bound concerns arbitrary finite cube dimensions; finite kernel checks certify small index and label obligations, not enumeration over dimensions.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.result`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricAAExclusion](SymmetricAAExclusion.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricBBExclusion](SymmetricBBExclusion.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricMixedExclusion](SymmetricMixedExclusion.md)
