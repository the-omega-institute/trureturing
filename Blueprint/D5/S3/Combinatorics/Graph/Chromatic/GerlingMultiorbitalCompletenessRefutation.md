# Failure of completeness for connected graphs with faithful C2 actions

## Abstract

Two connected finite graphs with faithful C2 actions share a multiorbital polynomial despite being nonisomorphic.

**Definition 1.1 (Restricted completeness assertion).**

$$\forall n \in \mathbb{N}, m \in \mathbb{N}, A \in \operatorname{GraphAction}\left(\operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right), n\right), B \in \operatorname{GraphAction}\left(\operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right), m\right),\; \operatorname{Connected}\left(A\right) \Rightarrow \left(\operatorname{Connected}\left(B\right) \Rightarrow \left(\operatorname{Faithful}\left(A\right) \Rightarrow \left(\operatorname{Faithful}\left(B\right) \Rightarrow \left(\operatorname{multiorbital}\left(A\right) = \operatorname{multiorbital}\left(B\right) \Rightarrow \operatorname{ActionIso}\left(A, B\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Melanie Gerling (2026). *The Multiorbital Bivariate Chromatic Polynomial: A Subgroup-Lattice Refinement*. URL: <https://arxiv.org/html/2609.01866v5>.

*Commentary.*

Fix the cyclic group of order two, represented by Multiplicative (ZMod 2). For natural numbers n and m, actions A and B have vertex sets Fin n and Fin m and preserve adjacency. Each input graph is finite, undirected and simple. Connected means that the underlying graph is connected. The predicate Faithful means that the homomorphism into its vertex permutation group is injective. ActionIso requires a graph isomorphism that intertwines the actions of each element of G. The antecedent uses equality in the rational polynomial ring in x and y.

A palette has x colors and its first y colors are proper. An edge forbids a shared proper color, including when its two endpoints coincide. At each group element, the fixed colorings descend to its cycle quotient. Taking the image of each unordered edge retains loops and merges parallel edges. For every subgroup, average the fixed-coloring counts over its elements, and sum the averages over all subgroups.

**Theorem 1.2 (A connected faithful C2 collision).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Melanie Gerling (2026). *The Multiorbital Bivariate Chromatic Polynomial: A Subgroup-Lattice Refinement*. URL: <https://arxiv.org/html/2609.01866v5>.

*Commentary.*

On vertices 0 through 5 use edges 03, 13, 04, 14, 23, 24, 25, 34 for the first graph and 02, 12, 05, 15, 23, 24, 25, 34 for the second. The generator of the group of order two acts by swapping 0 and 1 and fixing the other four vertices. In the first graph, vertex 2 reaches 0 and 1 through 3 and is adjacent to 3, 4 and 5. In the second graph, vertex 2 is adjacent to every other vertex. Both graphs are connected. Vertex 2 in the second graph has degree five. The degree multisets are (1,2,2,3,4,4) and (2,2,2,2,3,5), which rules out a graph isomorphism.

Label the orbit of 0 and 1 by 0, and label original vertices 2 through 5 by 1 through 4. The quotient edge lists are 02, 03, 12, 13, 14, 23 and 01, 04, 12, 13, 14, 23. The displayed lists contain no loops.

Inclusion–exclusion over the bad edge events gives one term for each subset S of edges. Each component incident to an edge of S contributes a factor of y, every other component contributes a factor of x, and the sign is negative exactly when S has odd cardinality. This also counts the effect of a loop by restricting the color of its component.

Both original graphs have polynomial P6 = x^6 − 8x^4y + 14x^3y + 11x^2y^2 − 20x^2y − 16xy^2 + 18xy − 2y^3 + 10y^2 − 8y. Both cycle quotients have P5 = x^5 − 6x^3y + 8x^2y + 5xy^2 − 8xy − 4y^2 + 4y. The trivial subgroup contributes P6, and the full group contributes the common orbital polynomial (P6 + P5)/2. The common multiorbital polynomial is (3P6 + P5)/2. All evaluations on admissible palettes determine a bivariate polynomial: for each natural y the infinitely many x ≥ y determine its polynomial in x, and the infinitely many y determine each of its coefficients in x.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation.result`
