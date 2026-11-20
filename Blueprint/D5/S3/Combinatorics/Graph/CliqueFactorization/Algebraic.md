# Algebraic clique factorization

## Abstract

Nonedge rectangles characterize clique factorization of commutative-group-valued functions.

Let V be a finite vertex type, Omega a family of arbitrary coordinate state spaces, A a commutative group, G a simple graph on V, and X the dependent product of the spaces Omega(i). Updating a configuration replaces one coordinate by a specified value. Neither the individual spaces nor X need be finite or inhabited.

In the formula, X is the dependent product of Omega(k) over k : V. DependsOn(h,S) means that h(x) = h(y) whenever x and y agree on every coordinate in S. IsClique(G,S) means that every two distinct vertices of S are adjacent. The product ranges over all finite subsets of V, including the empty set.

**Theorem 1.1 (Rectangle identities if and only if clique factors exist).**

$$\operatorname{universe} u v w; \forall V \in \operatorname{Type}\left(u\right),\; \forall Omega \in V \to \operatorname{Type}\left(v\right),\; \forall A \in \operatorname{Type}\left(w\right),\; [\operatorname{CommGroup}\left(A\right)] [\operatorname{Fintype}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall f \in (\prod_{k: V} \operatorname{Omega}\left(k\right)) \to A,\; (\forall i \in V,\; \forall j \in V,\; (i \ne j) \Rightarrow ((\neg(\operatorname{Adj}\left(G, i, j\right))) \Rightarrow (\forall x \in (\prod_{k: V} \operatorname{Omega}\left(k\right)),\; \forall a \in \operatorname{Omega}\left(i\right),\; \forall b \in \operatorname{Omega}\left(j\right),\; \operatorname{f}\left(x\right) \cdot \operatorname{f}\left(\operatorname{update}\left(\operatorname{update}\left(x, i, a\right), j, b\right)\right) = \operatorname{f}\left(\operatorname{update}\left(x, i, a\right)\right) \cdot \operatorname{f}\left(\operatorname{update}\left(x, j, b\right)\right)))) \Leftrightarrow (\exists Phi \in \operatorname{Finset}\left(V\right) \to \left((\prod_{k: V} \operatorname{Omega}\left(k\right)) \to A\right),\; (\forall S \in \operatorname{Finset}\left(V\right),\; \operatorname{DependsOn}\left(\operatorname{Phi}\left(S\right), S\right)) \land ((\forall S \in \operatorname{Finset}\left(V\right),\; (\neg(\operatorname{IsClique}\left(G, S\right))) \Rightarrow (\forall x \in (\prod_{k: V} \operatorname{Omega}\left(k\right)),\; \operatorname{Phi}\left(S, x\right) = 1)) \land (\forall x \in (\prod_{k: V} \operatorname{Omega}\left(k\right)),\; \operatorname{f}\left(x\right) = \prod_{S: \operatorname{Finset}\left(V\right)}\operatorname{Phi}\left(S, x\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CliqueFactorization/Algebraic.rectangle_iff_clique_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Geiger and Christopher Meek and Bernd Sturmfels (2006). *On the Toric Algebra of Graphical Models*. DOI: [10.1214/009053606000000263](https://doi.org/10.1214/009053606000000263). URL: <https://arxiv.org/pdf/math/0608054>.

*Commentary.*

The universes u, v and w are independent. Fintype(V) enumerates only vertices and their subsets; no finiteness condition is imposed on Omega(i). The same function f occurs in every rectangle and in reconstruction. A single factor family Phi simultaneously satisfies dependence, neutrality away from cliques, and reconstruction. Empty and singleton sets are cliques. Thus the empty factor may carry an arbitrary global constant, including when V is empty.

If X is empty, every assertion evaluated at a configuration is vacuous and all factors may be one. Otherwise choose an internal configuration o. For S a subset of V, clamp a configuration x to o outside S. Define kappa(S,x) as f of this clamp divided by the product of kappa(T,x) over all proper subsets T of S. Recursion on finite subsets defines one total family. Its values depend only on S, and cancellation reconstructs each clamped value as the product over every subset of S.

To show that a nonclique interaction is one, choose nonadjacent distinct vertices i and j in its support S and induct over proper subsets. Every proper subset containing both endpoints is a nonclique, so its interaction is one by induction. The remaining product is indexed by the union of the powersets of S without i and S without j. Their intersection is the powerset of S without both endpoints. The finite product union-intersection identity and the original rectangle at that doubly deleted clamp give the same product relation. Group cancellation forces kappa(S,x) to be one. This argument applies to any one family reconstructing all the anchored restrictions of the same f.

Conversely, each clique omits at least one endpoint of a nonedge. Dependence on the clique then makes its factor satisfy the rectangle identity. Nonclique factors are one. Multiplying these identities and using reconstruction at all four configurations yields the rectangle identity for f.

Geiger, Meek and Sturmfels, On the Toric Algebra of Graphical Models, Theorem 4.1, gives the Hammersley–Clifford equivalence for strictly positive finite discrete probability distributions. That restricted probability theorem supplies background, not the full statement here. The arbitrary-group argument above uses no normalization, order, topology, acyclicity or chordality. Factors are not asserted to be unique or supported only on maximal cliques. The theorem gives no algorithmic cost bound, probabilistic conditional-independence conclusion for arbitrary group values, or extension to semirings with zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CliqueFactorization/Algebraic.rectangle_iff_clique_factorization`
