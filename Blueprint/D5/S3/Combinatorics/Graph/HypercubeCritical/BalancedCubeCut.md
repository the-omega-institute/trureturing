# At least three edges in every positive balanced cubic cut

## Abstract

Every positive actual cut in a balanced induced cubic Q9 subgraph has at least three edges.

Hong–Wu–Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether f₂(Q₉)=3 or 4. This gives a necessary constraint on balanced cubic components of a candidate. It supplies no 258-vertex witness or complete exclusion; the existing 48- and 96-vertex bounds also leave that question unresolved.

**Definition 1.1 (Actual crossing cube edges counted once).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeCut.cutEdges`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeCut.cutEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cutEdges C T is T.sigma (fun x => (C \ T).filter (fun y => (hypercube 9).Adj x y)). When T ⊆ C it records exactly the actual cube edges from T to C \ T, each once with its endpoint in T first.

**Theorem 1.2 (Every positive cut has cardinality at least three).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeCut.three_le_cutEdges_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeCut.three_le_cutEdges_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For C,T : Finset Q9, assume the actual induced graph on C is regular of degree three, C satisfies the original FALSE-prefix BalancedCriticalSpectrum.IsBalanced, T ⊆ C, and 0 < (cutEdges C T).card. Then 3 ≤ (cutEdges C T).card. No connectedness hypothesis or connectedness conclusion is added; zero cuts are allowed outside the positive-cut hypothesis. Thus the statement does not assert unconditional three-edge connectivity of C.

Choose the switching function sigma on C and let the integer vector f equal sigma on T and zero elsewhere. The actual degree-three row equation and the signed edge products identify HuangIntegralNormGap.energy f with the actual cut cardinality. Positive cut size gives positive energy, so three_le_energy yields the claimed lower bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeCut.cutEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeCut.three_le_cutEdges_card`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangIntegralNormGap](HuangIntegralNormGap.md)
