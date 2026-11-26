# Multiplicity at negative one in a clique corona

## Abstract

A triangle with three leaves per center refutes the multiplicity bound.

**Definition 1.1 (Tagged centers and leaves).**

$$\forall t \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Vertex}\left(t, k\right) = \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Prod}\left(\operatorname{Fin}\left(t\right), \operatorname{Fin}\left(k\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A left tag marks a center. The two coordinates of a right tag give the owner and the leaf index at that owner.

**Definition 1.2 (Clique corona with independent leaf fibers).**

$$\forall t \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{corona}\left(t, k\right) : \operatorname{SimpleGraph}\left(\operatorname{Vertex}\left(t, k\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.corona` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two centers are adjacent exactly when their indices differ. A center and a leaf are adjacent exactly when the center is the leaf's owner, in either order. There are no edges between leaves. Symmetry and looplessness follow from these four cases.

$$
\forall t \in \mathbb{N},\; \forall k \in \mathbb{N},\; \begin{aligned}\forall i \in \operatorname{Fin}\left(t\right),\; \forall j \in \operatorname{Fin}\left(t\right),\; \operatorname{Adj}\left(\operatorname{corona}\left(t, k\right), \operatorname{inl}\left(i\right), \operatorname{inl}\left(j\right)\right) \Leftrightarrow i \ne j\\\forall i \in \operatorname{Fin}\left(t\right),\; \forall j \in \operatorname{Fin}\left(t\right),\; \forall b \in \operatorname{Fin}\left(k\right),\; \operatorname{Adj}\left(\operatorname{corona}\left(t, k\right), \operatorname{inl}\left(i\right), \operatorname{inr}\left((j, b)\right)\right) \Leftrightarrow i = j\\\forall i \in \operatorname{Fin}\left(t\right),\; \forall j \in \operatorname{Fin}\left(t\right),\; \forall a \in \operatorname{Fin}\left(k\right),\; \operatorname{Adj}\left(\operatorname{corona}\left(t, k\right), \operatorname{inr}\left((i, a)\right), \operatorname{inl}\left(j\right)\right) \Leftrightarrow j = i\\\forall i \in \operatorname{Fin}\left(t\right),\; \forall j \in \operatorname{Fin}\left(t\right),\; \forall a \in \operatorname{Fin}\left(k\right),\; \forall b \in \operatorname{Fin}\left(k\right),\; \operatorname{Adj}\left(\operatorname{corona}\left(t, k\right), \operatorname{inr}\left((i, a)\right), \operatorname{inr}\left((j, b)\right)\right) \Leftrightarrow False\end{aligned}
$$

**Definition 1.3 (Decidable adjacency).**

$$\forall t \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{DecidableRel}\left(\operatorname{Adj}\left(\operatorname{corona}\left(t, k\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.coronaDecidableAdj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four tag pairs reduce adjacency to inequation, equality, equality, or false. Finite-index equality supplies the decisions.

**Theorem 1.4 (Connectivity through the centers).**

$$\forall t \in \mathbb{N},\; \forall k \in \mathbb{N},\; 0 < t \Rightarrow \operatorname{Connected}\left(\operatorname{corona}\left(t, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.corona_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive t gives a center with index zero. Every other center is adjacent to it, and every leaf is adjacent to its own center. The condition t > 0 ensures a nonempty graph. No positivity assumption on k is needed.

**Theorem 1.5 (The actual independence polynomial).**

$$\forall t \in \mathbb{N},\; \forall k \in \mathbb{N},\; 0 < t \Rightarrow \operatorname{independencePolynomial}\left(\operatorname{corona}\left(t, k\right), univ\right) = (1 + X)^{(t - 1) \cdot k} \cdot ((1 + X)^{k} + (t : \operatorname{Polynomial}\left(\mathbb{Z}\right)) \cdot X)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.corona_factorization` (`✓ std3`). ∎

*Citation.* Vadim E. Levit; Eugen Mandrescu (2013). *On f-Symmetries of the Independence Polynomial*. DOI: [10.48550/arXiv.1303.2564](https://doi.org/10.48550/arXiv.1303.2564). URL: <https://arxiv.org/abs/1303.2564v1>.

*Commentary.*

The cast (t : Polynomial ℤ) is the constant polynomial given by the natural-number cast of t into ℤ[X]. The polynomial is the frozen independencePolynomial on the full vertex set. Each independent set contributes one monomial with degree its cardinality. The unique empty configuration contributes the constant coefficient one.

With no center chosen, all tk leaves are available. With a center chosen, its own leaves and all other centers are excluded. The remaining (t−1)k leaves are free. The proof uses the frozen partition deletion identity to split these actual configurations. The factorization is Gutman's corona formula specialized to the clique and the edgeless graph on k vertices, as stated by Levit and Mandrescu, Theorem 1.2.

**Theorem 1.6 (Exact multiplicity).**

$$\forall t \in \mathbb{N},\; \forall k \in \mathbb{N},\; 0 < t \Rightarrow \left(0 < k \Rightarrow \operatorname{rootMultiplicity}\left(-1, \operatorname{independencePolynomial}\left(\operatorname{corona}\left(t, k\right), univ\right)\right) = (t - 1) \cdot k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.corona_rootMultiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vadim E. Levit; Eugen Mandrescu (2013). *On f-Symmetries of the Independence Polynomial*. DOI: [10.48550/arXiv.1303.2564](https://doi.org/10.48550/arXiv.1303.2564). URL: <https://arxiv.org/abs/1303.2564v1>.

*Commentary.*

The exponent (t−1)k is exact because the residual evaluates to −t at −1. Positive k makes (1+X)^k vanish there. For k = 0 the residual instead evaluates to 1−t.

**Definition 1.7 (Question 5.8).**

$$Conjecture58 \Leftrightarrow (\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; 2 \le \operatorname{card}\left(V\right) \Rightarrow \left(\operatorname{Connected}\left(G\right) \Rightarrow (\operatorname{rootMultiplicity}\left(-1, \operatorname{independencePolynomial}\left(G, univ\right)\right) : \mathbb{Z}) \le \operatorname{ceil}\left(\frac{\operatorname{card}\left(V\right) : \mathbb{Q}}{2}\right) - 1\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.Conjecture58` (`✓ std3`).

*Citation.* Om Prakash Bhardwaj; Trung Chau; Sayeed Ikram; Gargi Lather; Vasudeva Nanjangud; Chitra Venugopal (2026). *Multiplicity of Negative One of Independence Polynomials of Graphs*. DOI: [10.48550/arXiv.2607.08480](https://doi.org/10.48550/arXiv.2607.08480). URL: <https://arxiv.org/abs/2607.08480v1>.

*Commentary.*

On page 16, Bhardwaj et al. ask whether a connected graph G on n ≥ 2 vertices must have mult₋₁ P_G ≤ ⌈n/2⌉ − 1. Page 1 specifies finite simple graphs and includes the empty independent set. The claim quantifies over a type V with a Fintype instance and every SimpleGraph G on V. Classical decidability imposes no additional graph hypothesis. Fintype.card V is the order, the division is in ℚ, and the ceiling, subtraction and comparison are in ℤ.

**Theorem 1.8 (A connected twelve-vertex counterexample).**

$$\neg Conjecture58$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Om Prakash Bhardwaj; Trung Chau; Sayeed Ikram; Gargi Lather; Vasudeva Nanjangud; Chitra Venugopal (2026). *Multiplicity of Negative One of Independence Polynomials of Graphs*. DOI: [10.48550/arXiv.2607.08480](https://doi.org/10.48550/arXiv.2607.08480). URL: <https://arxiv.org/abs/2607.08480v1>.

*Acknowledgement.* Vadim E. Levit; Eugen Mandrescu (2013). *On f-Symmetries of the Independence Polynomial*. DOI: [10.48550/arXiv.1303.2564](https://doi.org/10.48550/arXiv.1303.2564). URL: <https://arxiv.org/abs/1303.2564v1>.

*Commentary.*

Take t = k = 3. The graph is a triangle with three private leaves at each center. It has 3 + 3·3 = 12 vertices and is connected. Its polynomial is (1+X)^6((1+X)^3+3X), so the residual at −1 is −3 and the multiplicity is 6. The proposed bound is ⌈12/2⌉ − 1 = 5. The contradiction refutes Question 5.8.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.Conjecture58`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.Vertex`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.corona`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.coronaDecidableAdj`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.corona_connected`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.corona_factorization`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.corona_rootMultiplicity`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.result`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](IndependentPartitionDeletion.md)
