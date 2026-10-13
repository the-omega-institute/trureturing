# Rank from Maximum Matchings without Even Simple Cycles

## Abstract

Over every characteristic-two field, a symmetric zero-diagonal matrix whose support graph has no even simple cycle has rank twice its maximum matching cardinality.

Let V be any finite vertex type and K any field of characteristic two. A is symmetric with zero diagonal, and G.Adj(i,j) holds exactly when A(i,j) is nonzero. The cycle hypothesis concerns simple cycles, not all closed walks. An IsMatching subgraph has exactly one incident edge at every one of its vertices. Edges(M) is M.coe.edgeFinset, with unordered edges counted once.

**Theorem 1.1 (Rank Equals Twice the Maximum Matching Size).**

$$\forall V \in \mathrm{Type},\; \forall K \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] [\mathrm{Field}\left(K\right)] [\mathrm{CharP}\left(K, 2\right)] \forall A \in \mathrm{Matrix}\left(V, V, K\right),\; (\mathrm{IsSymm}\left(A\right)) \Rightarrow ((\forall i \in V,\; \mathrm{Entry}\left(A, i, i\right) = 0) \Rightarrow (\forall G \in \mathrm{SimpleGraph}\left(V\right),\; (\forall i \in V,\; \forall j \in V,\; (\mathrm{Adj}\left(G, i, j\right)) \Leftrightarrow (\mathrm{Entry}\left(A, i, j\right) \ne 0)) \Rightarrow ((\forall x \in V,\; \forall p \in \mathrm{Walk}\left(G, x, x\right),\; (\mathrm{IsCycle}\left(p\right)) \Rightarrow (\neg \mathrm{Even}\left(\mathrm{length}\left(p\right)\right))) \Rightarrow (\exists M \in \mathrm{Subgraph}\left(G\right),\; (\mathrm{IsMatching}\left(M\right)) \land ((\mathrm{rank}\left(A\right) = 2\times\mathrm{card}\left(\mathrm{Edges}\left(M\right)\right)) \land (\forall N \in \mathrm{Subgraph}\left(G\right),\; (\mathrm{IsMatching}\left(N\right)) \Rightarrow (\mathrm{card}\left(\mathrm{Edges}\left(N\right)\right) \le \mathrm{card}\left(\mathrm{Edges}\left(M\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/NoEvenCycleRank.rank_eq_twice_maximum_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem constructs a matching M, proves rank(A)=2|Edges(M)|, and proves |Edges(N)|<=|Edges(M)| for every matching N. Maximum means maximum cardinality. Two perfect matchings on any induced vertex set would give a nonempty symmetric difference consisting of even simple cycles. Thus each such set has at most one perfect matching. In the determinant sum, permutation inversion pairs non-involutions and cancels them in characteristic two. The remaining nonzero terms correspond to perfect matchings; uniqueness prevents cancellation. Selecting a basis of actual rows and using symmetry constructs a nonsingular principal restriction of size rank(A). Its perfect matching supplies M. Every matching N makes the restriction to its own vertices nonsingular, so 2|Edges(N)|<=rank(A). All intermediate constructions remain inside this proof.

For the stabilizer application, fix odd n>=3 and q>=2, N arbitrary, Grep=(Z/n)^(q-1), a primitive nth root zeta in an algebraic closure of F2, and F=F2(zeta). A character t has f_t(c)=t_c for c<q and f_t(q)=0. Let Gamma be any symmetric zero-diagonal F2 matrix and col:[N]->[q] any coloring, including empty parties. Put lambda_u=zeta^(f_t(col(u))), Lambda=diag(lambda), M=Lambda Gamma+Gamma Lambda over F, and let pi_t be the nonempty fibers of f_t. The mask B=Gamma^(pi_t) keeps Gamma_uv exactly when f_t(col(u)) differs from f_t(col(v)). Color inequality alone does not define this mask.

The primitive-root power injection proves lambda_u=lambda_v iff the character readouts agree. Characteristic two then gives lambda_u+lambda_v=0 iff they agree. Direct diagonal multiplication proves M_uv=Gamma_uv(lambda_u+lambda_v). The embedding F2->F is injective, so M and B have exactly the same nonzero support H_t, with H_t.Adj(u,v) iff Gamma_uv is nonzero and the readouts differ. Both matrices are symmetric and zero-diagonal. For any C subset of [N], restrict both rows and columns to C. If the induced graph H_t[C] has no even simple cycle, apply the content theorem over F to M[C] and independently over F2 to B[C]. Defining nu(H) as the maximum edge cardinality among all matching subgraphs gives rank_F M[C]=rank_F2 B[C]=2 nu(H_t[C]). The integer subtraction delta_C(t)=(rank_F M[C]:Z)-(rank_F2 B[C]:Z) is therefore zero.

C may be empty, disconnected, contain isolated vertices, or contain odd cycles. No perfect matching on all of C, connectivity, bipartiteness, or forest hypothesis is used. On the empty vertex type the determinant is one and the maximum matching and rank are zero. The graph-rank theorem itself requires only a characteristic-two field; finiteness of F and the replica inequalities belong to the original parameter setup. Graphs containing even simple cycles lie outside this theorem's support hypothesis. The weighted characteristic-two statement is a repository derivation; the classical forest adjacency-rank special case is not claimed as novel.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/NoEvenCycleRank.rank_eq_twice_maximum_matching`
