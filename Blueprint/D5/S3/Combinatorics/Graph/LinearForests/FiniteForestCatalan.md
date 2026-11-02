# The Catalan functional on finite linear forests

## Abstract

The alternating Catalan sum over all actual independent subsets of every finite acyclic graph of maximum degree two is nonnegative at every parameter at least its full vertex count.

**Theorem 1.1 (All vertices and all legal parameters).**

$$\forall V \in \mathrm{Type},\; \left(\operatorname{Fintype}\left(V\right) \land \operatorname{DecidableEq}\left(V\right)\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right) \Rightarrow \left(\forall m \in \mathrm{Nat},\; \left(\operatorname{IsAcyclic}\left(G\right) \land \left(\left(\forall v \in V,\; \operatorname{degree}\left(G, v\right) \le 2\right) \land \operatorname{card}\left(V\right) \le m\right)\right) \Rightarrow 0 \le \operatorname{phi}\left(G, \operatorname{univ}\left(V\right), m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/FiniteForestCatalan.finite_forest_phi_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be any finite vertex type with decidable equality, and let G be any simple graph on V with decidable adjacency. Assume that G is acyclic and that every vertex has degree at most two. For every natural m at least the cardinality of V, the integer phi(G,univ,m) is nonnegative. Here phi is PathCatalanFunctional.phi: it sums (-1) to card(S) times Catalan(m-card(S)) over all actual independent subsets S of the full vertex set. Empty graphs, arbitrary isolated vertices, arbitrarily many components and the boundary m=card(V) are included.

A longest simple path in a connected component contains every vertex. An edge leaving an endpoint would extend it; an edge leaving an interior vertex would give three distinct neighbors. The Hamiltonian vertex enumeration identifies the path graph with a spanning subgraph, and maximal acyclicity excludes additional edges. Induction over the remaining actual vertices concatenates these component enumerations into a bijection from the full vertex type to a finite interval, carrying every original edge to consecutive indices.

For two distinct nonadjacent vertices u and v in a finite domain W, write N_u and N_v for the respective closed-neighborhood complements within W. The independent-partition deletion identity, applied at u and then at v inside N_u, gives P_G=P_(G+uv)+w(u)w(v)P_(G on N_u intersect N_v). The added edge does not change adjacency on a domain omitting an endpoint. With each activity equal to -X, multiply by the integer Catalan series and take coefficient m. When m is at least card(W), this yields phi(G,W,m)=phi(G+uv,W,m)+phi(G,N_u intersect N_v,m-2). The residual domain has at most card(W)-2 vertices.

Induct first on the full actual vertex count and then on the number of missing edges in the spanning path. The added-edge term reduces the missing-edge count; the residual term is an actual induced forest on fewer vertices and has a legal shifted parameter. At the complete path, the configuration-preserving vertex bijection transports the functional directly to PathCatalanFunctional.path_phi_nonnegative. Its path recurrence and generating-series identity are reused through that theorem.

For the following applications, write C_n=catalan(n) and Phi_G(W,m)=phi G W m. Explicitly, Phi_G(W,m) is the integer sum of (-1)^|S| C_(m-|S|) over S contained in W for which no two distinct vertices of S are adjacent in G. Thus the indexing family is IndependentPartitionDeletion.configurations G W, with every subset of the actual domain considered, including subsets containing isolated vertices. Subtraction in the Catalan index is natural-number subtraction; throughout these applications m is at least |W|, so no index is truncated. Write Phi_G(m)=Phi_G(univ,m) when the full carrier is finite.

Same-carrier edge-extension comparison. Let alpha be any finite type with decidable equality, and let G and H be simple graphs on exactly alpha with decidable adjacency. If G is a subgraph of H, H is acyclic, every H degree is at most two, and m is a natural number with m at least card(alpha), then Phi_H(m) is at most Phi_G(m). The comparison retains every original vertex, including every original isolated vertex, in both full-domain sums. An isolate may acquire edges in H; it is never removed from the carrier.

To derive the comparison, let J be an intermediate subgraph of H and add an H edge uv absent from J. The endpoints are distinct. Form R=closedComplement J univ u intersect closedComplement J univ v using the old graph J: R consists of the vertices x other than u and v with neither J.Adj u x nor J.Adj v x. The supplier residual_card gives |R| at most card(alpha)-2 and 2 at most card(alpha). Hence |R| is at most card(alpha)-2, which is at most m-2. The graph induced by J on the actual subtype R is acyclic and has maximum degree at most two, since J is a subgraph of H. Apply finite_forest_phi_nonnegative at m-2 and then phi_subtype to obtain Phi_J(R,m-2) at least zero.

The supplier phi_add_edge now gives Phi_J(m)=Phi_(J+uv)(m)+Phi_J(R,m-2), so Phi_(J+uv)(m) is at most Phi_J(m). There are finitely many H edges missing from G. Adding them one at a time keeps every intermediate graph inside H and keeps alpha and m fixed; chaining the step inequalities gives Phi_H(m) at most Phi_G(m). Equivalently, represent intermediate graphs by finite subsets of H.edgeSet and apply Mathlib's Finset.antitone_iff_forall_insert_le. This is an application of the existing deletion, induced-domain transport and positivity suppliers.

The hypotheses fit the completion supplied by `D5/S3/Combinatorics/Graph/LinearForests/BipartiteCompletion.exists_saturating_extension`: for independent, disjoint parts A and B covering the full carrier, an acyclic G of maximum degree two, and |A|<|B|, that result supplies an H on the same carrier with G contained in H, the same forest and degree bounds, both parts still independent, and every A degree equal to two. The comparison applies to such an H for every m at least card(alpha). This gives a direction of comparison under completion; identifying completed graphs with a prescribed model family and proving extremality require the corresponding additional bridges.

The fixed-(4,7) three-odd-path models. Let p,q,r be nonnegative integers with p+q+r=4. Here P(n) means pathGraph n, with n vertices indexed from 0 to n-1 and edges exactly between consecutive indices. Define V(p,q,r)=Fin(2p+1) sum (Fin(2q+1) sum Fin(2r+1)) and the actual graph K(p,q,r)=P(2p+1) sum_graph (P(2q+1) sum_graph P(2r+1)) on that nested sum type. Each edge lies within one summand, so there are no edges between summands. In particular P(1) is an actual singleton component with degree zero, not an empty graph or a discarded factor.

The full model has 2(p+q+r)+3=11 vertices. In each summand put the odd local positions in A and the even local positions in B, retaining the summand tags. These are disjoint independent sets covering V(p,q,r), with |A|=p+q+r=4 and |B|=(p+1)+(q+1)+(r+1)=7. Every zero parameter contributes its singleton vertex to B. Evaluate Phi_K(16) over all independent subsets of these eleven vertices, including every such singleton.

All fifteen ordered triples are covered by the following exact evaluations. For (p,q,r)=(0,0,4),(0,4,0),(4,0,0), Phi_K(16)=29205; this value has ordered multiplicity three.

For (p,q,r)=(0,1,3),(0,3,1),(1,0,3),(1,3,0),(3,0,1),(3,1,0), Phi_K(16)=93159; this value has ordered multiplicity six.

For (p,q,r)=(0,2,2),(2,0,2),(2,2,0), Phi_K(16)=135149; this value has ordered multiplicity three.

For (p,q,r)=(1,1,2),(1,2,1),(2,1,1), Phi_K(16)=173909; this value has ordered multiplicity three. Each ordered equality evaluates the actual independent-subset sum, using C_n=binomial(2n,n)/(n+1); it does not assume a permutation-invariance theorem. These 3+6+3+3 cases exhaust p+q+r=4. Consequently Phi_K(16) is at least 29205 throughout this finite family, with equality exactly at (0,0,4),(0,4,0),(4,0,0).

An explicit full-carrier realization of the minimum is L=P(9) sum_graph bottom on Fin 9 sum Fin 2, where bottom has no edges. Its A vertices are the tagged path positions 1,3,5,7; its B vertices are path positions 0,2,4,6,8 and both tagged Fin 2 vertices. Thus |A|=4, |B|=7, every A degree is two, both extra vertices have degree zero, and L is acyclic with maximum degree two. Direct evaluation of the full eleven-vertex sum gives Phi_L(16)=29205.

The finite minimum concerns exactly the stated K family and the explicit L realization. Transferring it to an arbitrary original fixed-(4,7) forest still requires the exact original graph and partition correspondence, the full-carrier model transport for a permitted completion, and the resulting uniform extremality argument. The edge-extension comparison supplies an inequality once its graph hypotheses are met; the finite evaluations alone do not identify every original input with one of these models. The original native omitted-capacity bound 29205, its exact connection to Phi, and the original B44 numerical claim 69320276 remain unresolved here. C0, native acquisition and resource bounds likewise remain unresolved.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/BipartiteCompletion.exists_saturating_extension`
- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/FiniteForestCatalan.finite_forest_phi_nonnegative`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional](PathCatalanFunctional.md)
