# Rerouting Pair Selections

## Abstract

If each support has at least two vertices and every legal pair selection is sparse, some selection has only two-element supports on its four-cliques.

Let I and V be finite types, and let R(i) be a finite set of vertices for every owner i in I. A legal selection e chooses a two-element subset e(i) of R(i). Different owners may select the same pair. Sparse(e) means that for every vertex set S, twice the number of owners with e(i) contained in S is at most three times the cardinality of S. Thus parallel edges are counted with their owner multiplicities. Cliques(e) is the family of four-element vertex sets C whose six unordered pairs all occur among the selected pairs; each such C is counted once.

**Theorem 1.1 (A Minimum Selection Has Only Rigid Four-Cliques).**

$$\forall R \in \mathrm{Supports},\; \forall e \in \mathrm{Selections},\; (\mathrm{Selects}\left(R, e\right) \land \left(\mathrm{EverySelectionSparse}\left(R\right) \land \mathrm{MinimumCliqueCount}\left(R, e\right)\right)) \Rightarrow (\mathrm{RigidCliqueOwners}\left(R, e\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PairSelectionRerouting.minimal_selection_rigid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every legal selection is sparse, and e minimizes the number of four-cliques among legal selections. For each C in Cliques(e), every owner i with e(i) contained in C has exactly two vertices in R(i). The hypothesis concerns all selections, so it also supplies sparsity after changing one owner's pair.

A four-clique already uses six indexed owners on four vertices. Sparsity therefore makes every one of its six pairs have a unique owner. If an owner of uv has a third available vertex w, replace uv by uw. This destroys the old four-clique. When w lies inside it, the new simple edge was already present, so no clique is created. When w lies outside it, a newly created four-clique must contain uw. Its intersection with the old four vertices has size t equal to one, two, or three. Together with the five surviving old pairs, it gives at least 11 minus binomial(t,2) distinct edges on 8 minus t vertices. Each of the three cases violates sparsity. The rerouting therefore strictly reduces the clique family, contradicting minimality.

**Theorem 1.2 (Existence of a Rigid Selection).**

$$\forall R \in \mathrm{Supports},\; (\mathrm{SupportsAtLeastTwo}\left(R\right) \land \mathrm{EverySelectionSparse}\left(R\right)) \Rightarrow (\exists e \in \mathrm{Selections},\; \mathrm{Selects}\left(R, e\right) \land \mathrm{RigidCliqueOwners}\left(R, e\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PairSelectionRerouting.exists_rigid_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If each support has at least two vertices and every legal selection is sparse, a legal selection exists in which each owner on any four-clique has a two-element support. Choose a selection with the minimum clique count from the nonempty finite family of legal selections, and apply the preceding theorem. In particular, if all supports have at least three vertices, this selection has no four-clique. The conclusion is about pair selection and does not assert a coloring. Empty owner and vertex types are included whenever the stated hypotheses hold.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PairSelectionRerouting.exists_rigid_selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/PairSelectionRerouting.minimal_selection_rigid`
