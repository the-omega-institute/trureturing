# Nonbacktracking Leaf Walks Exhaust Their Components

## Abstract

An actual nonempty walk between leaves in a finite graph of degree at most two, with no immediate backtracking, is the entire simple path component.

Let G be a simple graph on a finite type V with decidable equality. Assume every neighbor set has at most two elements. Nonbacktracking(p) means that the actual vertices at positions i and i+2 differ whenever i+2 is within p's length. Nil(p) means that p has no edges. Sym2Mk(x,y) denotes the unordered pair s(x,y) used for graph edges. A leaf condition is expressed as a subsingleton neighbor set. It does not assume a chosen path, an endpoint matching or any component coverage.

**Theorem 1.1 (A Nonbacktracking Walk from a Leaf Is Simple).**

$$\forall V \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(V\right)] [\mathrm{Finite}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall a \in V,\; \forall b \in V,\; \forall p \in \mathrm{Walk}\left(G, a, b\right),\; ((\forall z \in V,\; \mathrm{ncard}\left(\mathrm{neighborSet}\left(G, z\right)\right) \le 2) \land ((\mathrm{Subsingleton}\left(\mathrm{neighborSet}\left(G, a\right)\right)) \land (\mathrm{Nonbacktracking}\left(p\right)))) \Rightarrow (\mathrm{IsPath}\left(p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/LeafNonbacktrackingComponent.nonbacktracking_leaf_isPath` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual walk starting at a leaf and having no immediate backtracking is a path. Strong induction on its actual length examines the prefix before the last edge. At each internal prefix vertex the two path neighbors exhaust the ambient neighbor set; at the starting leaf its one path neighbor does so. Returning to an earlier vertex would therefore use the prefix's last edge backwards, contradicting the actual nonbacktracking condition.

**Theorem 1.2 (A Nonempty Leaf-to-Leaf Walk Is the Whole Component).**

$$\forall V \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(V\right)] [\mathrm{Finite}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall a \in V,\; \forall b \in V,\; \forall p \in \mathrm{Walk}\left(G, a, b\right),\; (((\forall z \in V,\; \mathrm{ncard}\left(\mathrm{neighborSet}\left(G, z\right)\right) \le 2) \land ((\mathrm{Subsingleton}\left(\mathrm{neighborSet}\left(G, a\right)\right)) \land (\mathrm{Nonbacktracking}\left(p\right)))) \land ((\mathrm{Subsingleton}\left(\mathrm{neighborSet}\left(G, b\right)\right)) \land (\neg (\mathrm{Nil}\left(p\right))))) \Rightarrow ((\mathrm{IsPath}\left(p\right)) \land ((a \ne b) \land ((\mathrm{ncard}\left(\mathrm{neighborSet}\left(G, a\right)\right) = 1) \land ((\mathrm{ncard}\left(\mathrm{neighborSet}\left(G, b\right)\right) = 1) \land ((\forall x \in V,\; (x \in \mathrm{support}\left(p\right)) \Leftrightarrow (\mathrm{Reachable}\left(G, a, x\right))) \land (\forall x \in V,\; \forall y \in V,\; ((\mathrm{Adj}\left(G, x, y\right)) \land (\mathrm{Reachable}\left(G, a, x\right))) \Leftrightarrow (\mathrm{Sym2Mk}\left(x, y\right) \in \mathrm{edges}\left(p\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/LeafNonbacktrackingComponent.nonbacktracking_leaf_full_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the actual walk is nonempty and its endpoint also has a subsingleton neighbor set, its endpoints are distinct and each has exactly one neighbor. Its actual support consists exactly of the vertices reachable from its start. An ambient edge occurs in the actual walk exactly when its first endpoint is in that component. Other disconnected components are excluded. The first theorem earns the path condition. The endpoint leaf condition then saturates the final neighbor set as well, so no edge leaves the support. Induction along any actual reachable walk proves full component coverage.

Literal group-product traces give a sufficient condition for this theorem's nonbacktracking input. Let H be a group, val : V -> H any map, and word a list of group elements. Suppose p.support.map val equals the literal scanl trace starting at val(a), with the step (x,r) -> x*r. Equality of list lengths gives p.length = word.length. For i < word.length, indexing the scanl trace gives val(p.getVert(i+1)) = val(p.getVert(i))*word[i]. Assume every letter r in word satisfies r*r = 1, and consecutive letters differ. For i+2 <= p.length, if p.getVert(i) equals p.getVert(i+2), the two indexed steps and left cancellation give word[i]*word[i+1] = 1. Multiplying on the right by word[i+1] and using its involution law yields word[i] = word[i+1], a contradiction. Thus p has no immediate backtracking. This argument requires neither injectivity of val nor a Cayley-graph hypothesis. It uses List.getElem_succ_scanl and group cancellation; it is an application of existing results, not a separate new library theorem. The graph degree and leaf hypotheses remain necessary inputs to the two content theorems above.

For the prefix-reversal construction, this bridge turns a proved legal native word with different consecutive involutive generators and actual leaf endpoints into a complete path component after the cuts. One must still earn its degree bound, its leaf conditions and every legal native edge. Those native facts and the six-cut pairing are separate proof obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/LeafNonbacktrackingComponent.nonbacktracking_leaf_full_component`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/LeafNonbacktrackingComponent.nonbacktracking_leaf_isPath`
