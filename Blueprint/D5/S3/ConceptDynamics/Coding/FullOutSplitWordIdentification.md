# Full outgoing splits and legal words

## Abstract

Repeated full outgoing splits are legal-word graphs with their literal original-history windows.

**Theorem 1.1 (The original history at every depth).**

$$\forall F \in \mathit{Presentation}, n \in \mathit{Nat}, x \in \operatorname{Hist}\left(F\right), t \in \mathit{Int},\; \operatorname{edge}\left(\operatorname{identification}\left(F, n\right), \operatorname{val}\left(\operatorname{repeated}\left(F, n, x\right), t\right)\right) = \operatorname{historyWindow}\left(\operatorname{graph}\left(F\right), x, t, n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FullOutSplitWordIdentification.flatten_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the displays, graph(F) means F.graph, edge(r,e) means r.edge applied to e, val(y,t) means y.val at t, length(A) means A.length, and toHomeomorph(A,x) means A.toHomeomorph applied to x. Hist(F) is the type of legal two-sided histories of F. All depths are natural numbers and all times are integers.

Let G be a directed multigraph whose vertex and edge carriers share an arbitrary universe. The depth-zero block graph has the original vertex carrier and legal words of length one as edges, with the original source and target. At positive depth n, vertices are legal words of length n and edges are legal words of length n+1, with prefix and suffix endpoints. Word operations need no essentiality, finiteness or nonempty hypothesis.

Two adjacent block edges u,v reconstruct a word by prepending the first edge of u to v. The endpoint equality proves the first seam, including the separate depth-zero condition. Its prefix is u, its suffix is v, and joining the prefix and suffix of any word returns that word. For any graph relabeling r from H to the depth-n block graph, step constructs a relabeling from the full outgoing split of H to the depth-(n+1) block graph. A supported split vertex corresponds to its outgoing edge; a split edge corresponds to the joined pair of transported adjacent edges. Both vertex and edge inverse laws are proved from these actual finite-word operations.

For a finite essential Presentation F, stage F 0 is literally F and stage F (n+1) is the actual outgoing split of stage F n by the identity edge label. The recursively constructed identification fixes the original vertices at zero and constructs the graph relabeling at every positive depth. The map repeated is the composite of the actual split homeomorphisms; it starts with the identity. Each lift sends y at time t to the pair (y at t,y at t+1).

For every Presentation F, natural depth n, legal original history x and integer time t, flatten_window states that applying the edge part of identification F n to repeated F n x at t gives exactly historyWindow F.graph x t (n+1). Induction uses the predecessor identities at t and t+1. The first joined position is x at t, and every later position is x at t+j. The depth-zero case is the singleton original edge. Empty carriers and all zero depths remain in scope.

**Theorem 1.2 (An actual tower of the prescribed depth).**

$$\forall F \in \mathit{Presentation}, n \in \mathit{Nat},\; \operatorname{length}\left(\operatorname{tower}\left(F, n\right)\right) = n$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FullOutSplitWordIdentification.tower_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Presentation F and natural n, tower F n uses the existing outgoing and incoming Tower syntax and has length exactly n. Its zero case is the empty tower. The operation appendFull traverses any existing tower from F to K and appends one actual full outgoing split at K. Structural induction over both old constructor kinds proves that appendFull increases length by one; induction on n gives tower_length.

**Theorem 1.3 (The same repeated homeomorphism).**

$$\forall F \in \mathit{Presentation}, n \in \mathit{Nat}, x \in \operatorname{Hist}\left(F\right),\; \operatorname{toHomeomorph}\left(\operatorname{tower}\left(F, n\right), x\right) = \operatorname{repeated}\left(F, n, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FullOutSplitWordIdentification.tower_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Presentation F, natural n and original history x, the existing Tower.toHomeomorph of tower F n applied to x equals repeated F n x. For an arbitrary old tower from F to K, structural induction proves that appending the full split applies the actual outgoing lift at K after the old tower map. Induction on n then identifies the recursively constructed tower map with the composite used in flatten_window. No tower or desired bijection is supplied as a premise.

Legal-word extensionality and slice operations come from FiniteWindowTableCriterion. The actual supported partition lifts, finite presentations and tower syntax come from TwoSidedFiniteInduction. These formulas are derived for those constructions and make no literature-completeness or novelty claim. The conclusions concern arbitrary finite depths and retain the original history coordinates. The word-graph construction requires a common universe for the original vertex and edge carriers; every finite Presentation has both carriers in Type. No independent-universe extension with the same literal zero vertex carrier is asserted. Compatibility with numbered recoding, the full original conjugacy, SGCC, literal Fix(T^6), and minimum maximum period six remain outside these conclusions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FullOutSplitWordIdentification.flatten_window`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FullOutSplitWordIdentification.tower_apply`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FullOutSplitWordIdentification.tower_length`
- Dependency: [D5/S3/ConceptDynamics/Coding/TwoSidedFiniteInduction](TwoSidedFiniteInduction.md)
