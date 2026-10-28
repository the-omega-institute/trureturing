# Small-shift and unbounded total-domination roots

## Abstract

Actual total-domination roots approach minus one from the right and are unbounded to the left.

A total dominating set S is an actual finite subset of the graph vertices. Every vertex v, including every selected vertex, must have a neighbour u in S. No independence, minimality, ordinary closed-neighbourhood domination, or connectedness restriction on S is substituted. The polynomial coefficients count exactly these subsets.

**Definition 1.1 (Total domination).**

$$\forall (v:\operatorname{V}\left(\right)), \exists (u:\operatorname{V}\left(\right)), (u \in S) \land (\operatorname{Adj}\left(G, v, u\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.IsTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every actual graph G : SimpleGraph V and S : Finset V, IsTotal G S is the displayed proposition. V is implicit and has universe Type. The relation is the existing symmetric, loopless SimpleGraph adjacency.

**Definition 1.2 (The actual subset polynomial).**

$$\operatorname{totalPolynomial}\left(G\right) = \operatorname{sumTotalSubsets}\left(G\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.totalPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite V with a Fintype instance and every SimpleGraph G on V, totalPolynomial G lies in the real polynomial ring. sumTotalSubsets denotes the sum over all S : Finset V of X raised to S.card when IsTotal G S holds, and zero otherwise. There is no supplied polynomial hypothesis.

**Definition 1.3 (Disjoint union).**

$$\operatorname{unionGraph}\left(G, H\right) = \operatorname{disjointUnion}\left(G, H\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.unionGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G : SimpleGraph V and H : SimpleGraph W give a graph on V sum W. Two left vertices use G adjacency, two right vertices use H adjacency, and vertices on opposite sides are not adjacent. The private subset equivalence union_total and sum bijection union_polynomial prove multiplicativity.

**Definition 1.4 (A genuine universal vertex).**

$$\operatorname{coneGraph}\left(G\right) = \operatorname{cone}\left(G\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.coneGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex type is Unit sum V. The sole left vertex is adjacent to every right vertex; two right vertices use G adjacency; no left-left adjacency is allowed. For nonempty finite V, splitting subsets by hub membership proves T_cone(x)=x((1+x)^card(V)-1)+T_G(x). The selected hub itself requires a selected old vertex, which explains the subtraction of one.

**Definition 1.5 (The seed vertex types).**

$$\operatorname{SeedBase}\left(m\right) = \operatorname{recursiveSeedVertices}\left(m\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.SeedBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

m is any natural number. SeedBase 0 is Fin 3. SeedBase (m+1) is Fin 5 sum SeedBase m. Its exact cardinality is 5m+3. The explicit recursive Fintype instance supplies finite actual vertices at every unbounded order; the triangle supplies nonemptiness.

**Definition 1.6 (Five-cycles and a triangle).**

$$\operatorname{seedBaseGraph}\left(m\right) = \operatorname{cycleTriangleUnion}\left(m\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedBaseGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At m=0 this is the complete graph on Fin 3; at m+1 it is the disjoint union of the native cycleGraph 5 and seedBaseGraph m. Exact actual-subset enumeration gives T_C5=5x^3+5x^4+x^5 and T_K3=3x^2+x^3. Multiplicativity then gives their product for all m. These finite checks are consumed known ingredients of the unbounded seed estimate, not separate positive-instance results.

**Definition 1.7 (The actual seed graph).**

$$\operatorname{seedGraph}\left(m\right) = \operatorname{coneGraph}\left(\operatorname{seedBaseGraph}\left(m\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m, the result is a simple graph on Unit sum SeedBase m. It has 5m+4 vertices. The universal vertex and nonempty base give every vertex a neighbour.

**Definition 1.8 (The explicit seed polynomial).**

$$\operatorname{seedPolynomial}\left(m\right) = \operatorname{seedExpression}\left(m\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

seedExpression(m) means x((1+x)^(5m+3)-1)+(5x^3+5x^4+x^5)^m(3x^2+x^3) in R[X]. The private theorem seed_graph_polynomial identifies this expression with the actual subset totalPolynomial(seedGraph m); it is not an abstract replacement for that polynomial.

**Theorem 1.9 (A root in every shrinking interval).**

$$\forall (s:\mathbb{N}), ((3 \le s) \land (\operatorname{Odd}\left(s\right))) \Rightarrow (\exists (r:\mathbb{R}), (-1 < r) \land ((r < -1+\frac{1}{s}) \land (\operatorname{IsRoot}\left(\operatorname{seedPolynomial}\left(\operatorname{square}\left(s\right)\right), r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seed_root_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural s>=3 with Odd s, there is a real r strictly between -1 and -1+1/s at which seedPolynomial(s^2) vanishes. Write t=1/s, a=(1-t)^3(1+3t+t^2), and g=2-3t+t^3. The bounds 0<=a<=1-3t^2 and s^2*3t^2=3 imply a^(s^2)<=1/4 by Bernoulli, since a(1+3t^2)<=1. Also 0<=g<=2 and t^(5s^2+3)<=1/27. The hub term is at least 52/81 and the subtracted term at most 1/2, so the right endpoint value is positive. Oddness gives the left endpoint value -1. Continuity and the strict intermediate value theorem produce the root.

**Theorem 1.10 (The same roots belong to genuine isolate-free graphs).**

$$\forall (s:\mathbb{N}), ((3 \le s) \land (\operatorname{Odd}\left(s\right))) \Rightarrow (\exists (r:\mathbb{R}), ((-1 < r) \land ((r < -1+\frac{1}{s}) \land (\operatorname{IsRoot}\left(\operatorname{totalPolynomial}\left(\operatorname{seedGraph}\left(\operatorname{square}\left(s\right)\right)\right), r\right)))) \land ((\operatorname{totalPolynomial}\left(\operatorname{seedGraph}\left(\operatorname{square}\left(s\right)\right)\right) \neq 0) \land (\forall (v:\operatorname{sumType}\left(\operatorname{Unit}\left(\right), \operatorname{SeedBase}\left(\operatorname{square}\left(s\right)\right)\right)), \exists (u:\operatorname{sumType}\left(\operatorname{Unit}\left(\right), \operatorname{SeedBase}\left(\operatorname{square}\left(s\right)\right)\right)), \operatorname{Adj}\left(\operatorname{seedGraph}\left(\operatorname{square}\left(s\right)\right), v, u\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.actual_seed_root_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same s and interval witness r satisfy totalPolynomial(seedGraph(s^2)).IsRoot r, that actual polynomial is nonzero, and every actual vertex has a neighbour. Nonzeroness follows from its value -1 at -1. Thus selected vertices obey the total condition in a real graph; no zero polynomial or density hypothesis supplies the conclusion. The underlying graph has 5s^2+4 vertices. This theorem is one auxiliary step toward Shao-Zhao arXiv:2609.06569v5 section 5.2 Open Problem 2, registered as issue 23313. It does not prove roots dense in C: independent-fibre substitution, complex radial/angular approximation and final whole-plane assembly remain outside this statement.

**Theorem 1.11 (Exact finite labels).**

$$\operatorname{labelledSeedRoot}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.labelled_seed_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural s>=3 with Odd s, there exist a natural n, an actual SimpleGraph G on Fin n, and a real r such that n=5s^2+4, n>=2, -1<r<-1+1/s, T_G(r)=0, T_G is nonzero, and for every vertex v there exists a neighbour u. The exact same graph and polynomial satisfy all clauses. The proof transports finite subsets through the inverse Fintype.equivFin equivalence and preserves adjacency and cardinality.

**Theorem 1.12 (Arbitrarily small positive shifted roots).**

$$\forall (epsilon:\mathbb{R}), (0 < epsilon) \Rightarrow (\operatorname{actualSmallShift}\left(epsilon\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.arbitrarily_small_positive_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real epsilon there exist n, G : SimpleGraph (Fin n), and r : R with n>=2, 0<1+r<epsilon, T_G(r)=0, T_G nonzero, and every vertex having a neighbour. Choose k with 1/(k+1)<epsilon and the odd s=2k+3. Then 1/s<=1/(k+1), and labelled_seed_root supplies the witness. No order bound is imposed on n.

**Definition 1.13 (The literal complex-coefficient subset polynomial).**

$$\operatorname{complexPolynomial}\left(G\right) = \operatorname{complexSubsetSum}\left(G\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.complexPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type V and SimpleGraph G on V, complexSubsetSum is the sum over S : Finset V of the complex indeterminate X to S.card when IsTotal G S, and zero otherwise. It equals totalPolynomial G mapped by the real-to-complex ring homomorphism. Thus this is the same actual-subset counting definition in C[X].

**Definition 1.14 (The unchanged full target).**

$$\operatorname{WholePlaneDensity}\left(\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.WholePlaneDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unchanged proposition, consumed by TotalDominationDensity.result, states: for every complex z and every positive real epsilon, there exist n : N, G : SimpleGraph (Fin n), and w : C such that n>=2, every vertex has a neighbour, complexPolynomial G is nonzero, w is a root of that same polynomial, and norm(w-z)<epsilon. Every selected vertex must have a selected neighbour, as encoded in IsTotal. This retains the original all-z/all-epsilon, unbounded-order question.

**Theorem 1.15 (Complex roots accumulating at minus one).**

$$\forall (epsilon:\mathbb{R}), (0 < epsilon) \Rightarrow (\operatorname{actualComplexSeed}\left(epsilon\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.complex_seed_accumulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real epsilon there exist n, G : SimpleGraph (Fin n), and r : R such that n>=2, every vertex has a neighbour, complexPolynomial G is nonzero, the complex cast of r is its root, 0<1+r, and norm((r:C)-(-1:C))<epsilon. The same actual graph supplies all clauses. This follows by the injective real-to-complex coefficient map from arbitrarily_small_positive_shift. It proves accumulation at one point and supplies the centre case of TotalDominationDensity.result.

**Definition 1.16 (Disjoint-edge vertex types).**

$$\operatorname{EdgeBase}\left(m\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.EdgeBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m, EdgeBase 0 is Fin 2 and EdgeBase (m+1) is Fin 2 sum EdgeBase m. It has exactly 2(m+1) actual vertices and explicit finite and nonempty instances.

**Definition 1.17 (The actual disjoint matching).**

$$\operatorname{edgeBaseGraph}\left(m\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.edgeBaseGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The base at zero is the complete graph on two vertices. Each successor takes the disjoint union with another complete two-vertex graph. Actual total domination selects both ends of every edge, so its actual subset polynomial is X^(2(m+1)). This known finite identity is consumed by the unbounded-root construction.

**Definition 1.18 (The actual friendship graph).**

$$\operatorname{friendshipGraph}\left(m\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendshipGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is coneGraph(edgeBaseGraph m), on Unit sum EdgeBase m. All m+1 triangles share exactly the hub. The nonempty base and hub give a neighbour to every vertex, including the hub.

**Definition 1.19 (The known friendship expression).**

$$\operatorname{friendshipPolynomial}\left(m\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendshipPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m this is X*((1+X)^(2(m+1))-1)+X^(2(m+1)) in R[X]. The private friendship_graph_polynomial proves literal equality with totalPolynomial(friendshipGraph m) by actual subset counting. This is an attributed cone/friendship ingredient, not a separate new-identity or resolution claim.

**Theorem 1.20 (Actual total-domination roots are unbounded below).**

$$\operatorname{friendshipRootUnbounded}\left(R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendship_root_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real R>2 there exist a natural m and a real r<-R such that r is a root of totalPolynomial(friendshipGraph m), that same actual polynomial is nonzero, and every vertex has a neighbour. Put a=(1-1/R)^2 in [0,1), and choose m with a^(m+1)<1/R using the pinned Archimedean power theorem. At -R the polynomial equals R^(2(m+1))*(1-R*a^(m+1))+R>0. At -Q, Q=2(m+1)+2, Bernoulli gives Q*(1-1/Q)^(2(m+1))>=2, making its value negative. The same Bernoulli inequality implies R<=Q. Strict IVT on [-Q,-R] supplies r. The positive endpoint value proves nonzeroness. This supplies an unbounded real seed family for the unchanged whole target; it asserts no arbitrary complex approximation.

**Theorem 1.21 (Unbounded roots with exact finite labels).**

$$\operatorname{labelledUnboundedNegativeRoots}\left(R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.labelled_unbounded_negative_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real R>2 there exist n, G : SimpleGraph (Fin n), and r : R with n>=2, r<-R, every vertex having a neighbour, complexPolynomial G nonzero, and the complex cast of r a root of that same actual polynomial. The inverse Fintype.equivFin transports the friendship graph, its actual subsets, adjacency and cardinalities. The injective real-to-complex coefficient map preserves nonzeroness and roots. The graph has 2(m+1)+1 vertices for the m selected by friendship_root_unbounded.

The cycle, triangle, cone and disjoint-union identities are attributed ingredients: arXiv:1605.02222 and the H-join framework of Subramanian and Selvakumar, Filomat 2025. No worldwide priority or independent admission claim is made for this seed argument. The complete external question remains the density of nonzero total-domination roots of finite isolate-free graphs throughout the complex plane.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.EdgeBase`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.IsTotal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.SeedBase`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.WholePlaneDensity`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.actual_seed_root_right`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.arbitrarily_small_positive_shift`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.complexPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.complex_seed_accumulation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.coneGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.edgeBaseGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendshipGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendshipPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendship_root_unbounded`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.labelled_seed_root`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.labelled_unbounded_negative_roots`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedBaseGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seed_root_right`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.totalPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.unionGraph`
