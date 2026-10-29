# Small-shift and unbounded total-domination roots

## Abstract

Actual total-domination roots approach minus one from the right and are unbounded to the left.

A total dominating set S is an actual finite subset of the graph vertices. Every vertex v, including every selected vertex, must have a neighbour u in S. No independence, minimality, ordinary closed-neighbourhood domination, or connectedness restriction on S is substituted. The polynomial coefficients count exactly these subsets.

**Definition 1.1 (Total domination).**

$$\forall (V:\operatorname{Type}), \forall (G:\operatorname{SimpleGraph}\left(V\right)), \forall (S:\operatorname{Finset}\left(V\right)), (\operatorname{IsTotal}\left(G, S\right)) \Leftrightarrow (\forall (v:V), \exists (u:V), (u \in S) \land (\operatorname{Adj}\left(G, v, u\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.IsTotal` (`✓ std3`).

*Citation.* Saeid Alikhani; Nasrin Jafari (2016). *On the roots of total domination polynomial of graphs*. DOI: [10.48550/arXiv.1605.02222](https://doi.org/10.48550/arXiv.1605.02222). URL: <https://arxiv.org/html/1605.02222v1>.

*Commentary.*

For every actual graph G : SimpleGraph V and S : Finset V, IsTotal G S is the displayed proposition. V is implicit and has universe Type. The relation is the existing symmetric, loopless SimpleGraph adjacency.

**Definition 1.2 (The actual subset polynomial).**

$$\forall (V:\operatorname{Type}), [\operatorname{Fintype}\left(V\right)], \forall (G:\operatorname{SimpleGraph}\left(V\right)), \operatorname{totalPolynomial}\left(G\right) = \sum_{S:\operatorname{Finset}\left(V\right)} \operatorname{ite}\left(\operatorname{IsTotal}\left(G, S\right), ((X:\mathbb{R}[X]))^{\operatorname{card}\left(S\right)}, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.totalPolynomial` (`✓ std3`).

*Citation.* Saeid Alikhani; Nasrin Jafari (2016). *On the roots of total domination polynomial of graphs*. DOI: [10.48550/arXiv.1605.02222](https://doi.org/10.48550/arXiv.1605.02222). URL: <https://arxiv.org/html/1605.02222v1>.

*Commentary.*

For every finite V with a Fintype instance and every SimpleGraph G on V, totalPolynomial G lies in the real polynomial ring. The displayed sum ranges over all S : Finset V of X raised to S.card when IsTotal G S holds, and zero otherwise. There is no supplied polynomial hypothesis.

**Definition 1.3 (Disjoint union).**

$$\forall (V:\operatorname{Type}), \forall (W:\operatorname{Type}), \forall (G:\operatorname{SimpleGraph}\left(V\right)), \forall (H:\operatorname{SimpleGraph}\left(W\right)), (\forall (v:V), \forall (u:V), (\operatorname{Adj}\left(\operatorname{unionGraph}\left(G, H\right), \operatorname{inl}\left(v\right), \operatorname{inl}\left(u\right)\right)) \Leftrightarrow (\operatorname{Adj}\left(G, v, u\right))) \land ((\forall (a:W), \forall (b:W), (\operatorname{Adj}\left(\operatorname{unionGraph}\left(G, H\right), \operatorname{inr}\left(a\right), \operatorname{inr}\left(b\right)\right)) \Leftrightarrow (\operatorname{Adj}\left(H, a, b\right))) \land ((\forall (v:V), \forall (a:W), (\operatorname{Adj}\left(\operatorname{unionGraph}\left(G, H\right), \operatorname{inl}\left(v\right), \operatorname{inr}\left(a\right)\right)) \Leftrightarrow (\operatorname{False})) \land (\forall (a:W), \forall (v:V), (\operatorname{Adj}\left(\operatorname{unionGraph}\left(G, H\right), \operatorname{inr}\left(a\right), \operatorname{inl}\left(v\right)\right)) \Leftrightarrow (\operatorname{False}))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.unionGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G : SimpleGraph V and H : SimpleGraph W give a graph on V sum W. Two left vertices use G adjacency, two right vertices use H adjacency, and vertices on opposite sides are not adjacent. The private subset equivalence union_total and sum bijection union_polynomial prove multiplicativity.

**Definition 1.4 (A genuine universal vertex).**

$$\forall (V:\operatorname{Type}), \forall (G:\operatorname{SimpleGraph}\left(V\right)), (\forall (a:\operatorname{Unit}), \forall (b:\operatorname{Unit}), (\operatorname{Adj}\left(\operatorname{coneGraph}\left(G\right), \operatorname{inl}\left(a\right), \operatorname{inl}\left(b\right)\right)) \Leftrightarrow (\operatorname{False})) \land ((\forall (a:\operatorname{Unit}), \forall (v:V), (\operatorname{Adj}\left(\operatorname{coneGraph}\left(G\right), \operatorname{inl}\left(a\right), \operatorname{inr}\left(v\right)\right)) \Leftrightarrow (\operatorname{True})) \land ((\forall (v:V), \forall (a:\operatorname{Unit}), (\operatorname{Adj}\left(\operatorname{coneGraph}\left(G\right), \operatorname{inr}\left(v\right), \operatorname{inl}\left(a\right)\right)) \Leftrightarrow (\operatorname{True})) \land (\forall (v:V), \forall (u:V), (\operatorname{Adj}\left(\operatorname{coneGraph}\left(G\right), \operatorname{inr}\left(v\right), \operatorname{inr}\left(u\right)\right)) \Leftrightarrow (\operatorname{Adj}\left(G, v, u\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.coneGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex type is Unit sum V. The sole left vertex is adjacent to every right vertex; two right vertices use G adjacency; no left-left adjacency is allowed. For nonempty finite V, splitting subsets by hub membership proves T_cone(x)=x((1+x)^card(V)-1)+T_G(x). The selected hub itself requires a selected old vertex, which explains the subtraction of one.

**Definition 1.5 (Decidability of actual total domination).**

$$\forall (V:\operatorname{Type}), [\operatorname{Fintype}\left(V\right)], \forall (G:\operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (S:\operatorname{Finset}\left(V\right)), (\operatorname{totalDecidable}\left(G, S\right):\operatorname{Decidable}\left(\operatorname{IsTotal}\left(G, S\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.totalDecidable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public instance has exactly the displayed dependent type. Unfolding IsTotal reduces it to finite decidable universal and existential quantification over adjacency and membership.

**Definition 1.6 (SeedBase finite enumeration).**

$$\forall (m:\mathbb{N}), (\operatorname{seedBaseFintype}\left(m\right):\operatorname{Fintype}\left(\operatorname{SeedBase}\left(m\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedBaseFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m this is the displayed instance. At zero use the canonical Fin instance; at a successor use instFintypeSum with the recursively supplied instance.

**Definition 1.7 (SeedBase nonemptiness).**

$$\forall (m:\mathbb{N}), (\operatorname{seedBaseNonempty}\left(m\right):\operatorname{Nonempty}\left(\operatorname{SeedBase}\left(m\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedBaseNonempty` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m this is the displayed instance. At zero the finite base contains zero; at a successor the left summand contains zero.

**Definition 1.8 (The seed vertex types).**

$$(\operatorname{SeedBase}\left(0\right) = \operatorname{Fin}\left(3\right)) \land (\forall (m:\mathbb{N}), \operatorname{SeedBase}\left(m + 1\right) = \operatorname{Sum}\left(\operatorname{Fin}\left(5\right), \operatorname{SeedBase}\left(m\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.SeedBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

m is any natural number. SeedBase 0 is Fin 3. SeedBase (m+1) is Fin 5 sum SeedBase m. Its exact cardinality is 5m+3. The explicit recursive Fintype instance supplies finite actual vertices at every unbounded order; the triangle supplies nonemptiness.

**Definition 1.9 (Five-cycles and a triangle).**

$$(\operatorname{seedBaseGraph}\left(0\right) = (\operatorname{top}:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(3\right)\right))) \land (\forall (m:\mathbb{N}), \operatorname{seedBaseGraph}\left(m + 1\right) = \operatorname{unionGraph}\left(\operatorname{cycleGraph}\left(5\right), \operatorname{seedBaseGraph}\left(m\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedBaseGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At m=0 this is the complete graph on Fin 3; at m+1 it is the disjoint union of the native cycleGraph 5 and seedBaseGraph m. Exact actual-subset enumeration gives T_C5=5x^3+5x^4+x^5 and T_K3=3x^2+x^3. Multiplicativity then gives their product for all m. These finite checks are consumed known ingredients of the unbounded seed estimate, not separate positive-instance results.

**Definition 1.10 (The actual seed graph).**

$$\forall (m:\mathbb{N}), \operatorname{seedGraph}\left(m\right) = \operatorname{coneGraph}\left(\operatorname{seedBaseGraph}\left(m\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m, the result is a simple graph on Unit sum SeedBase m. It has 5m+4 vertices. The universal vertex and nonempty base give every vertex a neighbour.

**Definition 1.11 (The explicit seed polynomial).**

$$\forall (m:\mathbb{N}), (\operatorname{seedPolynomial}\left(m\right):\mathbb{R}[X]) = X \cdot \left((1 + X)^{5 \cdot m + 3} - 1\right) + (5 \cdot (X)^{3} + 5 \cdot (X)^{4} + (X)^{5})^{m} \cdot \left(3 \cdot (X)^{2} + (X)^{3}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression is x((1+x)^(5m+3)-1)+(5x^3+5x^4+x^5)^m(3x^2+x^3) in R[X]. The private theorem seed_graph_polynomial identifies this expression with the actual subset totalPolynomial(seedGraph m); it is not an abstract replacement for that polynomial.

**Theorem 1.12 (A root in every shrinking interval).**

$$\forall (s:\mathbb{N}), (3 \le s) \Rightarrow ((\operatorname{Odd}\left(s\right)) \Rightarrow (\exists (r:\mathbb{R}), (-1 < r) \land ((r < -1 + \frac{1}{(s:\mathbb{R})}) \land (\operatorname{IsRoot}\left(\operatorname{seedPolynomial}\left((s)^{2}\right), r\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seed_root_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural s>=3 with Odd s, there is a real r strictly between -1 and -1+1/s at which seedPolynomial(s^2) vanishes. Write t=1/s, a=(1-t)^3(1+3t+t^2), and g=2-3t+t^3. The bounds 0<=a<=1-3t^2 and s^2*3t^2=3 imply a^(s^2)<=1/4 by Bernoulli, since a(1+3t^2)<=1. Also 0<=g<=2 and t^(5s^2+3)<=1/27. The hub term is at least 52/81 and the subtracted term at most 1/2, so the right endpoint value is positive. Oddness gives the left endpoint value -1. Continuity and the strict intermediate value theorem produce the root.

**Theorem 1.13 (The same roots belong to genuine isolate-free graphs).**

$$\forall (s:\mathbb{N}), (3 \le s) \Rightarrow ((\operatorname{Odd}\left(s\right)) \Rightarrow (\exists (r:\mathbb{R}), (-1 < r) \land ((r < -1 + \frac{1}{(s:\mathbb{R})}) \land ((\operatorname{IsRoot}\left(\operatorname{totalPolynomial}\left(\operatorname{seedGraph}\left((s)^{2}\right)\right), r\right)) \land ((\operatorname{totalPolynomial}\left(\operatorname{seedGraph}\left((s)^{2}\right)\right) \ne 0) \land (\forall (v:\operatorname{Sum}\left(\operatorname{Unit}, \operatorname{SeedBase}\left((s)^{2}\right)\right)), \exists (u:\operatorname{Sum}\left(\operatorname{Unit}, \operatorname{SeedBase}\left((s)^{2}\right)\right)), \operatorname{Adj}\left(\operatorname{seedGraph}\left((s)^{2}\right), v, u\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.actual_seed_root_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same s and interval witness r satisfy totalPolynomial(seedGraph(s^2)).IsRoot r, that actual polynomial is nonzero, and every actual vertex has a neighbour. Nonzeroness follows from its value -1 at -1. Thus selected vertices obey the total condition in a real graph; no zero polynomial or density hypothesis supplies the conclusion. The underlying graph has 5s^2+4 vertices. This theorem supplies the small shifted roots for the complex density argument. It does not prove roots dense in C: independent-fibre substitution, complex radial/angular approximation and final whole-plane assembly remain outside this statement.

**Theorem 1.14 (Exact finite labels).**

$$\forall (s:\mathbb{N}), (3 \le s) \Rightarrow ((\operatorname{Odd}\left(s\right)) \Rightarrow (\exists (n:\mathbb{N}), \exists (G:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \exists (r:\mathbb{R}), (n = 5 \cdot (s)^{2} + 4) \land ((2 \le n) \land ((-1 < r) \land ((r < -1 + \frac{1}{(s:\mathbb{R})}) \land ((\operatorname{IsRoot}\left(\operatorname{totalPolynomial}\left(G\right), r\right)) \land ((\operatorname{totalPolynomial}\left(G\right) \ne 0) \land (\forall (v:\operatorname{Fin}\left(n\right)), \exists (u:\operatorname{Fin}\left(n\right)), \operatorname{Adj}\left(G, v, u\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.labelled_seed_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural s>=3 with Odd s, there exist a natural n, an actual SimpleGraph G on Fin n, and a real r such that n=5s^2+4, n>=2, -1<r<-1+1/s, T_G(r)=0, T_G is nonzero, and for every vertex v there exists a neighbour u. The exact same graph and polynomial satisfy all clauses. The proof transports finite subsets through the inverse Fintype.equivFin equivalence and preserves adjacency and cardinality.

**Theorem 1.15 (Arbitrarily small positive shifted roots).**

$$\forall (epsilon:\mathbb{R}), (0 < epsilon) \Rightarrow (\exists (n:\mathbb{N}), \exists (G:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \exists (r:\mathbb{R}), (2 \le n) \land ((0 < 1 + r) \land ((1 + r < epsilon) \land ((\operatorname{IsRoot}\left(\operatorname{totalPolynomial}\left(G\right), r\right)) \land ((\operatorname{totalPolynomial}\left(G\right) \ne 0) \land (\forall (v:\operatorname{Fin}\left(n\right)), \exists (u:\operatorname{Fin}\left(n\right)), \operatorname{Adj}\left(G, v, u\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.arbitrarily_small_positive_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real epsilon there exist n, G : SimpleGraph (Fin n), and r : R with n>=2, 0<1+r<epsilon, T_G(r)=0, T_G nonzero, and every vertex having a neighbour. Choose k with 1/(k+1)<epsilon and the odd s=2k+3. Then 1/s<=1/(k+1), and labelled_seed_root supplies the witness. No order bound is imposed on n.

**Definition 1.16 (The literal complex-coefficient subset polynomial).**

$$\forall (V:\operatorname{Type}), [\operatorname{Fintype}\left(V\right)], \forall (G:\operatorname{SimpleGraph}\left(V\right)), \operatorname{complexPolynomial}\left(G\right) = \sum_{S:\operatorname{Finset}\left(V\right)} \operatorname{ite}\left(\operatorname{IsTotal}\left(G, S\right), ((X:\mathbb{C}[X]))^{\operatorname{card}\left(S\right)}, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.complexPolynomial` (`✓ std3`).

*Citation.* Saeid Alikhani; Nasrin Jafari (2016). *On the roots of total domination polynomial of graphs*. DOI: [10.48550/arXiv.1605.02222](https://doi.org/10.48550/arXiv.1605.02222). URL: <https://arxiv.org/html/1605.02222v1>.

*Commentary.*

For every finite vertex type V and SimpleGraph G on V, complexPolynomial G is the sum over S : Finset V of the complex indeterminate X to S.card when IsTotal G S, and zero otherwise. It equals totalPolynomial G mapped by the real-to-complex ring homomorphism. Thus this is the same actual-subset counting definition in C[X].

**Definition 1.17 (The unchanged full target).**

$$(\operatorname{WholePlaneDensity}) \Leftrightarrow (\forall (z:\mathbb{C}), \forall (epsilon:\mathbb{R}), (0 < epsilon) \Rightarrow (\exists (n:\mathbb{N}), \exists (G:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \exists (w:\mathbb{C}), (2 \le n) \land ((\forall (v:\operatorname{Fin}\left(n\right)), \exists (u:\operatorname{Fin}\left(n\right)), \operatorname{Adj}\left(G, v, u\right)) \land ((\operatorname{complexPolynomial}\left(G\right) \ne 0) \land ((\operatorname{IsRoot}\left(\operatorname{complexPolynomial}\left(G\right), w\right)) \land (\Vert w - z\Vert < epsilon))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.WholePlaneDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *On the Roots of Connected Domination Polynomials*. DOI: [10.48550/arXiv.2609.06569](https://doi.org/10.48550/arXiv.2609.06569). URL: <https://arxiv.org/html/2609.06569v5>.

*Commentary.*

The unchanged proposition, consumed by TotalDominationDensity.result, states: for every complex z and every positive real epsilon, there exist n : N, G : SimpleGraph (Fin n), and w : C such that n>=2, every vertex has a neighbour, complexPolynomial G is nonzero, w is a root of that same polynomial, and norm(w-z)<epsilon. Every selected vertex must have a selected neighbour, as encoded in IsTotal. This retains the original all-z/all-epsilon, unbounded-order question.

**Theorem 1.18 (Complex roots accumulating at minus one).**

$$\forall (epsilon:\mathbb{R}), (0 < epsilon) \Rightarrow (\exists (n:\mathbb{N}), \exists (G:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \exists (r:\mathbb{R}), (2 \le n) \land ((\forall (v:\operatorname{Fin}\left(n\right)), \exists (u:\operatorname{Fin}\left(n\right)), \operatorname{Adj}\left(G, v, u\right)) \land ((\operatorname{complexPolynomial}\left(G\right) \ne 0) \land ((\operatorname{IsRoot}\left(\operatorname{complexPolynomial}\left(G\right), (r:\mathbb{C})\right)) \land ((0 < 1 + r) \land (\Vert (r:\mathbb{C}) - (-1:\mathbb{C})\Vert < epsilon))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.complex_seed_accumulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real epsilon there exist n, G : SimpleGraph (Fin n), and r : R such that n>=2, every vertex has a neighbour, complexPolynomial G is nonzero, the complex cast of r is its root, 0<1+r, and norm((r:C)-(-1:C))<epsilon. The same actual graph supplies all clauses. This follows by the injective real-to-complex coefficient map from arbitrarily_small_positive_shift. It proves accumulation at one point and supplies the centre case of TotalDominationDensity.result.

**Definition 1.19 (EdgeBase finite enumeration).**

$$\forall (m:\mathbb{N}), (\operatorname{edgeBaseFintype}\left(m\right):\operatorname{Fintype}\left(\operatorname{EdgeBase}\left(m\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.edgeBaseFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m this is the displayed instance. At zero use the canonical Fin instance; at a successor use instFintypeSum with the recursively supplied instance.

**Definition 1.20 (EdgeBase nonemptiness).**

$$\forall (m:\mathbb{N}), (\operatorname{edgeBaseNonempty}\left(m\right):\operatorname{Nonempty}\left(\operatorname{EdgeBase}\left(m\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.edgeBaseNonempty` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m this is the displayed instance. At zero the finite base contains zero; at a successor the left summand contains zero.

**Definition 1.21 (Disjoint-edge vertex types).**

$$(\operatorname{EdgeBase}\left(0\right) = \operatorname{Fin}\left(2\right)) \land (\forall (m:\mathbb{N}), \operatorname{EdgeBase}\left(m + 1\right) = \operatorname{Sum}\left(\operatorname{Fin}\left(2\right), \operatorname{EdgeBase}\left(m\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.EdgeBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m, EdgeBase 0 is Fin 2 and EdgeBase (m+1) is Fin 2 sum EdgeBase m. It has exactly 2(m+1) actual vertices and explicit finite and nonempty instances.

**Definition 1.22 (The actual disjoint matching).**

$$(\operatorname{edgeBaseGraph}\left(0\right) = (\operatorname{top}:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(2\right)\right))) \land (\forall (m:\mathbb{N}), \operatorname{edgeBaseGraph}\left(m + 1\right) = \operatorname{unionGraph}\left((\operatorname{top}:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(2\right)\right)), \operatorname{edgeBaseGraph}\left(m\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.edgeBaseGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The base at zero is the complete graph on two vertices. Each successor takes the disjoint union with another complete two-vertex graph. Actual total domination selects both ends of every edge, so its actual subset polynomial is X^(2(m+1)). This known finite identity is consumed by the unbounded-root construction.

**Definition 1.23 (The actual friendship graph).**

$$\forall (m:\mathbb{N}), \operatorname{friendshipGraph}\left(m\right) = \operatorname{coneGraph}\left(\operatorname{edgeBaseGraph}\left(m\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendshipGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is coneGraph(edgeBaseGraph m), on Unit sum EdgeBase m. All m+1 triangles share exactly the hub. The nonempty base and hub give a neighbour to every vertex, including the hub.

**Definition 1.24 (The known friendship expression).**

$$\forall (m:\mathbb{N}), (\operatorname{friendshipPolynomial}\left(m\right):\mathbb{R}[X]) = X \cdot \left((1 + X)^{2 \cdot \left(m + 1\right)} - 1\right) + (X)^{2 \cdot \left(m + 1\right)}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendshipPolynomial` (`✓ std3`).

*Citation.* Saeid Alikhani; Nasrin Jafari (2016). *On the roots of total domination polynomial of graphs*. DOI: [10.48550/arXiv.1605.02222](https://doi.org/10.48550/arXiv.1605.02222). URL: <https://arxiv.org/html/1605.02222v1>.

*Commentary.*

For every natural m this is X*((1+X)^(2(m+1))-1)+X^(2(m+1)) in R[X]. The private friendship_graph_polynomial proves literal equality with totalPolynomial(friendshipGraph m) by actual subset counting. Alikhani and Jafari, arXiv:1605.02222v1 Theorem 2.1(ii), give x(x+1)^(2n)+x^(2n)-x for n>=2. Our n=m+1 matches that range exactly when m>=1. The m=0 triangle base is proved locally by actual subset enumeration, giving 3X^2+X^3; it is not a literal attestation of that theorem beyond its range.

**Theorem 1.25 (Actual total-domination roots are unbounded below).**

$$\forall (R:\mathbb{R}), (2 < R) \Rightarrow (\exists (m:\mathbb{N}), \exists (r:\mathbb{R}), (r < -R) \land ((\operatorname{IsRoot}\left(\operatorname{totalPolynomial}\left(\operatorname{friendshipGraph}\left(m\right)\right), r\right)) \land ((\operatorname{totalPolynomial}\left(\operatorname{friendshipGraph}\left(m\right)\right) \ne 0) \land (\forall (v:\operatorname{Sum}\left(\operatorname{Unit}, \operatorname{EdgeBase}\left(m\right)\right)), \exists (u:\operatorname{Sum}\left(\operatorname{Unit}, \operatorname{EdgeBase}\left(m\right)\right)), \operatorname{Adj}\left(\operatorname{friendshipGraph}\left(m\right), v, u\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendship_root_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real R>2 there exist a natural m and a real r<-R such that r is a root of totalPolynomial(friendshipGraph m), that same actual polynomial is nonzero, and every vertex has a neighbour. Put a=(1-1/R)^2 in [0,1), and choose m with a^(m+1)<1/R using the pinned Archimedean power theorem. At -R the polynomial equals R^(2(m+1))*(1-R*a^(m+1))+R>0. At -Q, Q=2(m+1)+2, Bernoulli gives Q*(1-1/Q)^(2(m+1))>=2, making its value negative. The same Bernoulli inequality implies R<=Q. Strict IVT on [-Q,-R] supplies r. The positive endpoint value proves nonzeroness. This supplies an unbounded real seed family for the unchanged whole target; it asserts no arbitrary complex approximation.

**Theorem 1.26 (Unbounded roots with exact finite labels).**

$$\forall (R:\mathbb{R}), (2 < R) \Rightarrow (\exists (n:\mathbb{N}), \exists (G:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \exists (r:\mathbb{R}), (2 \le n) \land ((r < -R) \land ((\forall (v:\operatorname{Fin}\left(n\right)), \exists (u:\operatorname{Fin}\left(n\right)), \operatorname{Adj}\left(G, v, u\right)) \land ((\operatorname{complexPolynomial}\left(G\right) \ne 0) \land (\operatorname{IsRoot}\left(\operatorname{complexPolynomial}\left(G\right), (r:\mathbb{C})\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.labelled_unbounded_negative_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real R>2 there exist n, G : SimpleGraph (Fin n), and r : R with n>=2, r<-R, every vertex having a neighbour, complexPolynomial G nonzero, and the complex cast of r a root of that same actual polynomial. The inverse Fintype.equivFin transports the friendship graph, its actual subsets, adjacency and cardinalities. The injective real-to-complex coefficient map preserves nonzeroness and roots. The graph has 2(m+1)+1 vertices for the m selected by friendship_root_unbounded.

The friendship expression and total-domination definition are attested in Alikhani and Jafari. The cycle, triangle, cone and disjoint-union formulas are proved here from actual subsets and used as ingredients; these local proofs assert no original discovery of those identities. The complex target is the question of Shao and Zhao, section 5.2 Open Problem 2.

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
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.edgeBaseFintype`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.edgeBaseGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.edgeBaseNonempty`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendshipGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendshipPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.friendship_root_unbounded`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.labelled_seed_root`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.labelled_unbounded_negative_roots`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedBaseFintype`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedBaseGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedBaseNonempty`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seedPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.seed_root_right`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.totalDecidable`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.totalPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.unionGraph`
