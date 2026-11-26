# Leaf-support joining and the domination polynomial product

## Abstract

Joining leaf supports of graphs along any graph keeps dominating sets componentwise, so the domination polynomials multiply.

**Definition 1.1 (The leaf-support join).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/LeafSupportJoin.join`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LeafSupportJoin.join` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Alikhani–Griswold, Section 4(3): connected graphs with domination root −4*. DOI: [10.5281/zenodo.23919066](https://doi.org/10.5281/zenodo.23919066). URL: <https://doi.org/10.5281/zenodo.23919066>.

*Commentary.*

For graphs H_i on vertex types V_i, chosen vertices v_i and a simple graph F on the indices, the join J_F lives on the disjoint union of the V_i. Two vertices of one copy are adjacent when they are adjacent in that copy, and the only edges between copies are v_i v_j for ij an edge of F.

**Theorem 1.2 (Componentwise domination).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/LeafSupportJoin.leaf_support_join`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/LeafSupportJoin.leaf_support_join` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Alikhani–Griswold, Section 4(3): connected graphs with domination root −4*. DOI: [10.5281/zenodo.23919066](https://doi.org/10.5281/zenodo.23919066). URL: <https://doi.org/10.5281/zenodo.23919066>.

*Commentary.*

Suppose every copy has a vertex w_i whose only neighbour is v_i. A set dominates J_F exactly when each of its slices dominates the corresponding copy: a vertex dominated across copies is a support v_i, and v_i is already dominated inside its copy because w_i must be dominated there, by itself or by v_i. Restriction and disjoint union are therefore inverse bijections preserving total size, and D(J_F,x) = ∏ D(H_i,x) in ℤ[x], the empty product being 1. If there is at least one copy and every H_i and F is connected, every vertex reaches its support, and supports reach each other along F, so J_F is connected. This is Lemma 1 of H. Ma and W. Zhang; the added edges are irrelevant edges in the sense of Kotek, Preen, Simon, Tittmann and Trinks.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LeafSupportJoin.join`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LeafSupportJoin.leaf_support_join`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverage](../DominatingSetAverage.md)
