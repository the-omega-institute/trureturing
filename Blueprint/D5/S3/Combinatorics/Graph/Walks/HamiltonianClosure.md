# Hamiltonian closure and Ore's theorem

## Abstract

Endpoint degree sums close spanning paths, preserve Hamiltonicity under one closure edge, and imply Ore's theorem.

Let V be an arbitrary finite vertex type in any universe and G a simple undirected graph on V. Write n for its cardinality and deg(G,v) for the cardinality of the neighbor set of v. The Lean statements use Fintype, decidable equality, and decidable adjacency to present these finite objects; classical instances supply those presentations without additional mathematical restrictions. IsHamiltonian and IsHamiltonianCycle are the native graph and walk predicates.

**Theorem 1.1 (A spanning path closes after rerouting).**

$$\forall V \in \mathrm{Type},\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall a \in V,\; \forall b \in V,\; \forall p \in \operatorname{Walk}\left(G, a, b\right),\; \left(\operatorname{IsHamiltonian}\left(p\right) \land \left(3 \le \operatorname{card}\left(V\right) \land \operatorname{card}\left(V\right) \le \operatorname{degree}\left(G, a\right) + \operatorname{degree}\left(G, b\right)\right)\right) \Rightarrow \left(\exists c \in \operatorname{Walk}\left(G, a, a\right),\; \operatorname{IsHamiltonianCycle}\left(c\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/HamiltonianClosure.exists_hamiltonian_cycle_of_path` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

For every a,b in V and every actual G-walk p from a to b, assume p is Hamiltonian, n is at least three, and deg(G,a)+deg(G,b) is at least n. There exists an actual Hamiltonian cycle based at a. No edge between a and b is assumed.

Enumerate the spanning path as x(0),...,x(n-1). Among the n-1 positions between consecutive vertices, the positions i with a adjacent to x(i+1) number deg(G,a), and those with b adjacent to x(i) number deg(G,b). Their sum exceeds n-1, so the two sets meet. At such an i, keep the prefix through x(i), connect to b, follow the reversed suffix to x(i+1), and return to a. The prefix support and the reversed suffix support partition every vertex exactly once. The native path-ring splicing theorem constructs the actual cycle from these pieces and the two real connecting edges.

**Theorem 1.2 (Bondy--Chvatal single-edge closure).**

$$\forall V \in \mathrm{Type},\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall u \in V,\; \forall v \in V,\; \left(u \ne v \land \left(\left(\neg \operatorname{Adj}\left(G, u, v\right)\right) \land \operatorname{card}\left(V\right) \le \operatorname{degree}\left(G, u\right) + \operatorname{degree}\left(G, v\right)\right)\right) \Rightarrow \left(\operatorname{IsHamiltonian}\left(\operatorname{sup}\left(G, \operatorname{edge}\left(u, v\right)\right)\right) \Leftrightarrow \operatorname{IsHamiltonian}\left(G\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/HamiltonianClosure.isHamiltonian_sup_edge_iff` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

For every u,v in V, if u differs from v, u and v are nonadjacent in G, and n is at most deg(G,u)+deg(G,v), then G sup edge(u,v) is Hamiltonian if and only if G is Hamiltonian. Both degrees belong to G before adding the edge. There is no connectedness or external lower-cardinality hypothesis. Empty, singleton, and two-vertex types remain included under the stated premises.

Distinct nonadjacent endpoints each have degree at most n-2, and the degree-sum bound therefore implies n is at least three. If a Hamilton cycle of the augmented graph uses the added edge, open that actual edge with the native cycle-slicing theorem. The resulting spanning path uses only original edges, transfers back to G, and closes by endpoint rerouting. If the cycle does not use the added edge, transfer it directly. The opposite implication is graph monotonicity.

**Theorem 1.3 (Ore's degree-sum criterion).**

$$\forall V \in \mathrm{Type},\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \left(3 \le \operatorname{card}\left(V\right) \land \left(\forall u \in V,\; \forall v \in V,\; \left(u \ne v \land \left(\neg \operatorname{Adj}\left(G, u, v\right)\right)\right) \Rightarrow \operatorname{card}\left(V\right) \le \operatorname{degree}\left(G, u\right) + \operatorname{degree}\left(G, v\right)\right)\right) \Rightarrow \operatorname{IsHamiltonian}\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/HamiltonianClosure.ore` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

If n is at least three and every distinct nonadjacent pair u,v in V satisfies n at most deg(G,u)+deg(G,v), then G is Hamiltonian. The quantifier covers all such pairs in an arbitrary finite graph. No minimum-degree or connectedness strengthening is imposed.

Induct on the finite number of ordered distinct nonadjacent pairs. If there are none, G is complete and the native complete-graph theorem applies. Otherwise add one absent edge. The number of missing ordered pairs strictly decreases, and degree monotonicity preserves the Ore condition. Apply the induction hypothesis to the augmented graph and the single-edge closure equivalence to return to G.

These are known theorems of Bondy and Chvatal and of Ore. The proof adapts Juan Pablo Traverso Gianini's MengerHamilton/ClosureAux.lean and Hamiltonian.lean at immutable jtraverso/menger-hamiltonian commit 35c5f684f9bfbd244bd0999ce725623ab571adb6. It retains the endpoint index-counting and missing-edge induction arguments while using the receiver's native Walk interfaces, cycle opening and path-ring splicing. The donor's cyclic-arrangement framework, complete-graph construction, Menger, Dirac and Chvatal--Erdos developments are outside this result. The source note gives the original paper locators, software attribution, license and retirement condition. No originality or reading of the original full papers is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/HamiltonianClosure.exists_hamiltonian_cycle_of_path`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/HamiltonianClosure.isHamiltonian_sup_edge_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/HamiltonianClosure.ore`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PathRingSplicing](PathRingSplicing.md)
