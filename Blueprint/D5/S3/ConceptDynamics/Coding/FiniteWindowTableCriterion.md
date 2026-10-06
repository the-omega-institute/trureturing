# Complete arbitrary-table criterion

## Abstract

Four concrete word tests characterize the same arbitrary pair of finite-window tables as mutually inverse continuous maps commuting with the original unit shift.

**Theorem 1.1 (Exactly the supplied tables on all histories).**

$$\forall V \in Type, E \in Type, W \in Type, D \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), F \in \operatorname{DirectedMultigraph}\left(W, D\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), equalityV \in \operatorname{DecidableEq}\left(V\right), finiteW \in \operatorname{Fintype}\left(W\right), finiteD \in \operatorname{Fintype}\left(D\right), equalityW \in \operatorname{DecidableEq}\left(W\right), topologyE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right), topologyD \in \operatorname{TopologicalSpace}\left(D\right), discreteD \in \operatorname{DiscreteTopology}\left(D\right), nonemptyV \in \operatorname{Nonempty}\left(V\right), nonemptyW \in \operatorname{Nonempty}\left(W\right), p \in Nat, q \in Nat, r \in Nat, s \in Nat, essentialG \in \operatorname{Essential}\left(G\right), essentialF \in \operatorname{Essential}\left(F\right), pair \in \operatorname{TablePair}\left(G, F, p, q, r, s\right),\; \operatorname{LocalCriterion}\left(pair\right) \Leftrightarrow \operatorname{Nonempty}\left(\operatorname{SameTableConjugacy}\left(pair\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.original23_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent natural radii p,q,r,s may all be zero. Write m=p+q+1, n=r+s+1 and N=p+q+r+s+1. TablePair contains arbitrary f:LegalWord(G,m) to D and g:LegalWord(F,n) to E; it imposes no encoding hypothesis. SeamG checks every m+1 edge word and equates target(f(slice(word,0,m))) with source(f(slice(word,1,m))). SeamF is the corresponding n+1 edge equation for g.

For every G word of length N, mapBlock applies f to the n windows starting at j=0 through n minus 1. Its legality is proved from seamG before g is applied. The equation then says g(mapBlock(f,word))=word[p+r]. The F test applies g to the m windows starting at j=0 through m minus 1, proves legality from seamF, and says f(mapBlock(g,word))=word[p+r]. Both input intervals are exactly [-p-r,q+s]. Proof irrelevance makes the equations independent of the seam-proof choice.

SameTableConjugacy carries two legal-history maps with pointwise bindings Phi(x)[i]=f(historyWindow(G,x,i-p,m)) and Psi(y)[i]=g(historyWindow(F,y,i-r,n)). It also carries both inverse equations, continuity in the product subspace topology of discrete actual edges, and both commutation laws with the shift x[i] to x[i+1]. Necessity uses the retained two-tail realizer on each prescribed word. Its actual occurrences force both seam equations and both center recoveries. The same f and g occur in all these statements.

**Theorem 1.2 (Local and global equivariance for the same maps).**

$$\forall V \in Type, E \in Type, W \in Type, D \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), F \in \operatorname{DirectedMultigraph}\left(W, D\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), equalityV \in \operatorname{DecidableEq}\left(V\right), finiteW \in \operatorname{Fintype}\left(W\right), finiteD \in \operatorname{Fintype}\left(D\right), equalityW \in \operatorname{DecidableEq}\left(W\right), Gamma \in Type, group \in \operatorname{Group}\left(Gamma\right), actionV \in \operatorname{MulAction}\left(Gamma, V\right), actionE \in \operatorname{MulAction}\left(Gamma, E\right), actionW \in \operatorname{MulAction}\left(Gamma, W\right), actionD \in \operatorname{MulAction}\left(Gamma, D\right), AG \in \operatorname{GraphAction}\left(Gamma, G\right), AF \in \operatorname{GraphAction}\left(Gamma, F\right), topologyE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right), topologyD \in \operatorname{TopologicalSpace}\left(D\right), discreteD \in \operatorname{DiscreteTopology}\left(D\right), nonemptyV \in \operatorname{Nonempty}\left(V\right), nonemptyW \in \operatorname{Nonempty}\left(W\right), p \in Nat, q \in Nat, r \in Nat, s \in Nat, essentialG \in \operatorname{Essential}\left(G\right), essentialF \in \operatorname{Essential}\left(F\right), pair \in \operatorname{TablePair}\left(G, F, p, q, r, s\right),\; \left(\operatorname{LocalCriterion}\left(pair\right) \land \left(\operatorname{LocalEquivariant}\left(AG, \operatorname{f}\left(pair\right)\right) \land \operatorname{LocalEquivariant}\left(AF, \operatorname{g}\left(pair\right)\right)\right)\right) \Leftrightarrow \left(\exists c \in \operatorname{SameTableConjugacy}\left(pair\right),\; \operatorname{GlobalEquivariant}\left(AG, AF, \operatorname{forward}\left(c\right)\right) \land \operatorname{GlobalEquivariant}\left(AF, AG, \operatorname{backward}\left(c\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.original23_1_equivariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

GraphAction states source and target preservation for the supplied vertex and edge actions. Word and history actions act on each actual edge. LocalEquivariant quantifies every group element and every window, with f(a acting on word)=a acting on f(word), and likewise for g. GlobalEquivariant states the same equality for the same history maps. Necessity realizes each word; the chosen tails need not themselves be equivariant. The equivalence holds for any group, and the finite algorithm uses a finite group.

**Theorem 1.3 (Terminating finite checks with actual failure facts).**

$$\forall V \in Type, E \in Type, W \in Type, D \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), F \in \operatorname{DirectedMultigraph}\left(W, D\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), equalityV \in \operatorname{DecidableEq}\left(V\right), finiteW \in \operatorname{Fintype}\left(W\right), finiteD \in \operatorname{Fintype}\left(D\right), equalityW \in \operatorname{DecidableEq}\left(W\right), equalityE \in \operatorname{DecidableEq}\left(E\right), equalityD \in \operatorname{DecidableEq}\left(D\right), p \in Nat, q \in Nat, r \in Nat, s \in Nat, pair \in \operatorname{TablePair}\left(G, F, p, q, r, s\right), edgesG \in \operatorname{List}\left(E\right), edgesF \in \operatorname{List}\left(D\right), completeG \in \left(\forall e \in E,\; e \in edgesG\right), completeF \in \left(\forall d \in D,\; d \in edgesF\right), essentialG \in \operatorname{Essential}\left(G\right), essentialF \in \operatorname{Essential}\left(F\right),\; \left(\neg \operatorname{LocalCriterion}\left(pair\right)\right) \Leftrightarrow \left(\exists bad \in \operatorname{FailureWitness}\left(pair\right),\; \operatorname{FailureExposure}\left(bad\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.rejected_candidate_has_finite_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With decidable vertex and edge equality, legalWordFintype enumerates exactly the subtype of finite edge tuples satisfying adjacency, and tablePairFintype enumerates every pair of actual functions. The seam tests run before the dependent roundtrip tests. finiteTableExists decides existence at fixed radii by finite quantification over these table pairs. originalExistenceDecidable transports that executable decision to existence of a SameTableConjugacy; the analogous finite-group functions include all group/window equations.

For certificate extraction the caller supplies complete finite edge lists and a complete group list. tupleWords recursively enumerates tuples; enumerateWords keeps exactly legal words, with a proved completeness theorem. List.choose scans these explicit lists for a failing fact. Every FailureWitness contains a word and the actual failed seam or recovery equality, including the seam proofs needed to type a recovery. EquivariantFailure adds the actual group element, window and failed action equality. The inspector returns either all test proofs or the failed finite test. The rejection theorem equates rejection with existence of such a concrete failure exposed in an actual history; the corresponding finite-group theorem includes group/window failures and their history occurrences. No arbitrary classical Decidable, sampling criterion or graph-only uniform bound on radii is asserted.

Loops, parallel edges, disconnected essential components and asymmetric windows stay in scope. All checked word lengths are positive; no statement identifies a zero-edge path with a vertex-free empty edge tuple. The parameter specialization 23.2 introduces no retained wrapper. The unsupported 21.3 claim and the existing matrix-chain construction are outside this module. Authored formulas summarize the exact declarations using the defined record names; SDK admission, script execution and rendering alone do not establish semantic equivalence or canonical admission.

**Definition 1.4 (Actual free expansion).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right),\; \operatorname{DirectedMultigraph}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(n\right), H\right), \operatorname{Prod}\left(\operatorname{Edge}\left(A\right), H\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.countedExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any square natural group-ring matrix A, the vertex of an expanded edge (e,h) is (source(e),h), and its target is (target(e),h times label(e)). This definition is definitionally equal to the existing FixedBlockRigidity.expandedGraph; it imposes no commutativity and forgets no numbered edge.

**Definition 1.5 (orderedForward).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right),\; \operatorname{LegalWord}\left(\operatorname{countedExpansion}\left(\operatorname{product}\left(U, V\right)\right), 2\right) \to \operatorname{Prod}\left(\operatorname{Edge}\left(\operatorname{product}\left(V, U\right)\right), H\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedForward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the legal two-edge word ((a0,h0),(a1,h1)), split both edges in the prescribed UV order as (u0,v0),(u1,v1). Return (joinVU(v0,u1),h0 times label(u0)). Adjacency supplies the actual shared vertex for joining. This crosses the first actual U half-edge.

**Definition 1.6 (orderedBackward).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right),\; \operatorname{LegalWord}\left(\operatorname{countedExpansion}\left(\operatorname{product}\left(V, U\right)\right), 2\right) \to \operatorname{Prod}\left(\operatorname{Edge}\left(\operatorname{product}\left(U, V\right)\right), H\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedBackward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two input edges are preceding and central output. Split them in VU order as (vMinus,u0),(v0,u1). Return (joinUV(u0,v0),k0 times label(u0) inverse), where k0 is the coordinate of the SECOND input edge. The shared U half-edge is constructed by splitting the preceding output, not assumed as an inverse map.

**Definition 1.7 (orderedOverlapInput).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right),\; \operatorname{TablePair}\left(\operatorname{countedExpansion}\left(\operatorname{product}\left(U, V\right)\right), \operatorname{countedExpansion}\left(\operatorname{product}\left(V, U\right)\right), 0, 1, 1, 0\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedOverlapInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This raw TablePair uses orderedForward and orderedBackward on the actual free expansions of UV and VU, at forward radii (0,1) and inverse radii (1,0). No successful criterion is embedded. The transient structural check tests the same maps on three-edge words and recovers center index one.

**Definition 1.8 (d8Rank).**

$$\operatorname{DihedralGroup}\left(4\right) \to Nat$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.d8Rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

d8Rank(r i)=i.val and d8Rank(sr i)=4+(-i).val. Since sr i denotes s times r to i, this is exactly e,r,r squared,r cubed,s,rs,r squared s,r cubed s. d8Rank_injective is the consumed private proof used by d8Order, which lifts the natural order through this rank.

**Definition 1.9 (d8Order).**

$$\operatorname{LinearOrder}\left(\operatorname{DihedralGroup}\left(4\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.d8Order` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total order is lifted through the injective d8Rank. It is a finite group order for labels and does not claim a multiplication-compatible group order.

**Definition 1.10 (d8P).**

$$\operatorname{GroupMat}\left(\operatorname{DihedralGroup}\left(4\right), 1, 1\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.d8P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the source order the scalar factor P has coefficients [1,2,1,1,1,1,1,0]. Each nonzero coefficient is a literal MonoidAlgebra.single summand; the r cubed s coefficient is zero.

**Definition 1.11 (d8Q).**

$$\operatorname{GroupMat}\left(\operatorname{DihedralGroup}\left(4\right), 1, 1\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.d8Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar factor Q is the sum of the literal unit-labelled and s-labelled singleton coefficients, each one. Its vector is [1,0,0,0,1,0,0,0].

**Definition 1.12 (orderedD8Input).**

$$\operatorname{TablePair}\left(\operatorname{countedExpansion}\left(\operatorname{product}\left(d8P, d8Q\right)\right), \operatorname{countedExpansion}\left(\operatorname{product}\left(d8Q, d8P\right)\right), 0, 1, 1, 0\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedD8Input` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The independently existing original20.1/20.3/22.2/23.2 problem uses these literal factors, their actual products, prescribed split ranks and asymmetric orderedOverlapInput tables. This declaration is raw input only. Acceptance, coefficient specialization, radii specialization and the same-table soundness application remain transient exact evidence; no positive instance theorem is retained.

**Definition 1.13 (d8Groups).**

$$\operatorname{List}\left(\operatorname{DihedralGroup}\left(4\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.d8Groups` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete dictionary is [r0,r1,r2,r3,sr0,sr3,sr2,sr1], exactly the prescribed source order. Completeness is checked transiently.

**Definition 1.14 (orderedEdges).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right),\; \operatorname{List}\left(\operatorname{Prod}\left(\operatorname{Edge}\left(A\right), H\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a square matrix A, enumerate group coordinate h, source i, target j, label g in their supplied finite orders, then every c in Fin(coeff(A[i,j],g)). The list contains every actual expanded numbered edge, including every nonzero fiber and no element of an empty fiber. Its completeness is checked before the inspector call.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.countedExpansion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.d8Groups`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.d8Order`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.d8P`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.d8Q`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.d8Rank`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedBackward`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedD8Input`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedEdges`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedForward`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedOverlapInput`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.original23_1`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.original23_1_equivariant`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.rejected_candidate_has_finite_witness`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupOverlap](CountedGroupOverlap.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/EssentialWordRealization](EssentialWordRealization.md)
