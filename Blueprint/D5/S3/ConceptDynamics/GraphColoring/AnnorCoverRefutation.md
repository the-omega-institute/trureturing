# Refutation of Annor Conjecture 14

## Abstract

No universal positive constant bounds cover domination below by fold times base domination.

The source asserts the existence of a universal positive constant. The following refutation is repository work, with novelty suspected only after a bounded literature check. It requires independent review. Known product-graph and perfect-code ingredients are not counted as separate results.

**Theorem 1.1 (A strict violation for every constant).**

$$\begin{gathered}\forall c: \mathbb{R},0<c \Rightarrow \\{}\exists V: \operatorname{Type},W: \operatorname{Type},fv: \operatorname{Fintype}\left(V\right),fw: \operatorname{Fintype}\left(W\right),\\{}F: \operatorname{SimpleGraph}\left(V\right),G: \operatorname{SimpleGraph}\left(W\right),p: W \to V,k: \mathbb{N},\\{}(\operatorname{Connected}\left(F\right)) \land (0<k) \land (\operatorname{IsCover}\left(G, F, p, k\right)) \land (\operatorname{dominationNumber}\left(G\right)<c \cdot k \cdot \operatorname{dominationNumber}\left(F\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.exists_cover_violation` (`✓ std3`). ∎

*Source.* Suspected novel.

*Acknowledgement.* Dickson Y. B. Annor (2025). *Domination Parameters of Graph Covers*. DOI: [10.48550/arXiv.2502.14341](https://doi.org/10.48550/arXiv.2502.14341).

*Commentary.*

V and W range over finite types, and F and G are undirected simple graphs. IsCover means an onto map, a bijection on each open neighborhood, and fiber cardinality k. Domination numbers and k are coerced from naturals to reals in the inequality. The witnesses have connected bases and positive folds; the source does not require G connected. With t=r+1, the base has order (2t+1)^t, degree (2t)^t and domination at least t. The cover domination is at most the base order. Bernoulli gives base order at most twice its degree. Choosing r greater than 2/c makes the violation strict for any positive c.

**Theorem 1.2 (No universal constant).**

$$\begin{gathered}\neg(\exists c: \mathbb{R},(0<c) \land (\forall V: \operatorname{Type},W: \operatorname{Type},fv: \operatorname{Fintype}\left(V\right),fw: \operatorname{Fintype}\left(W\right),\\{}F: \operatorname{SimpleGraph}\left(V\right),G: \operatorname{SimpleGraph}\left(W\right),p: W \to V,k: \mathbb{N},\\{}0<k \Rightarrow \operatorname{IsCover}\left(G, F, p, k\right) \Rightarrow c \cdot k \cdot \operatorname{dominationNumber}\left(F\right) \le \operatorname{dominationNumber}\left(G\right)))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.annor_conjecture14_false` (`✓ std3`). ∎

*Source.* Suspected novel.

*Acknowledgement.* Dickson Y. B. Annor (2025). *Domination Parameters of Graph Covers*. DOI: [10.48550/arXiv.2502.14341](https://doi.org/10.48550/arXiv.2502.14341).

*Commentary.*

V and W range over finite types, and F and G are undirected simple graphs. IsCover means an onto map, a bijection on each open neighborhood, and fiber cardinality k. Domination numbers and k are coerced from naturals to reals in the inequality. The witnesses have connected bases and positive folds; the source does not require G connected. With t=r+1, the base has order (2t+1)^t, degree (2t)^t and domination at least t. The cover domination is at most the base order. Bernoulli gives base order at most twice its degree. Choosing r greater than 2/c makes the violation strict for any positive c.

Vertex(r,m) is the function type Fin(r+1) to Fin(m+1). Two vertices are adjacent exactly when they differ in every coordinate. The product is categorical, not Cartesian. Its domination theory is established in the cited literature; these elementary ingredients are not claimed novel.

**Theorem 1.3 (Degree).**

$$\begin{gathered}\forall r: \mathbb{N},m: \mathbb{N},\operatorname{IsRegularOfDegree}\left(\operatorname{productGraph}\left(r, m\right), m^{(r+1)}\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.productGraph_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Harish Vemuri (2019). *Domination in Direct Products of Complete Graphs*. DOI: [10.48550/arXiv.1908.02445](https://doi.org/10.48550/arXiv.1908.02445).

*Commentary.*

The proof uses finite coordinate choices and cardinalities. For domination, assign one distinct coordinate to each selected vertex and use an unused coordinate to stay outside the selected set. For density, apply Bernoulli's inequality to one minus the reciprocal of 2(r+1)+1.

**Theorem 1.4 (Connectedness).**

$$\begin{gathered}\forall r: \mathbb{N},m: \mathbb{N},2 \le m \Rightarrow \operatorname{Connected}\left(\operatorname{productGraph}\left(r, m\right)\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.productGraph_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Harish Vemuri (2019). *Domination in Direct Products of Complete Graphs*. DOI: [10.48550/arXiv.1908.02445](https://doi.org/10.48550/arXiv.1908.02445).

*Commentary.*

The proof uses finite coordinate choices and cardinalities. For domination, assign one distinct coordinate to each selected vertex and use an unused coordinate to stay outside the selected set. For density, apply Bernoulli's inequality to one minus the reciprocal of 2(r+1)+1.

**Theorem 1.5 (Domination lower bound).**

$$\begin{gathered}\forall r: \mathbb{N},m: \mathbb{N},r \le m \Rightarrow (r+1) \le \operatorname{dominationNumber}\left(\operatorname{productGraph}\left(r, m\right)\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.productGraph_domination_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Harish Vemuri (2019). *Domination in Direct Products of Complete Graphs*. DOI: [10.48550/arXiv.1908.02445](https://doi.org/10.48550/arXiv.1908.02445).

*Commentary.*

The proof uses finite coordinate choices and cardinalities. For domination, assign one distinct coordinate to each selected vertex and use an unused coordinate to stay outside the selected set. For density, apply Bernoulli's inequality to one minus the reciprocal of 2(r+1)+1.

**Theorem 1.6 (Uniform density).**

$$\begin{gathered}\forall r: \mathbb{N},((2 \cdot (r+1))+1)^{(r+1)} \le 2 \cdot (2 \cdot (r+1))^{(r+1)}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.productGraph_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Harish Vemuri (2019). *Domination in Direct Products of Complete Graphs*. DOI: [10.48550/arXiv.1908.02445](https://doi.org/10.48550/arXiv.1908.02445).

*Commentary.*

The proof uses finite coordinate choices and cardinalities. For domination, assign one distinct coordinate to each selected vertex and use an unused coordinate to stay outside the selected set. For density, apply Bernoulli's inequality to one minus the reciprocal of 2(r+1)+1.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.annor_conjecture14_false`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.exists_cover_violation`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.productGraph_connected`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.productGraph_density`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.productGraph_domination_lower`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.productGraph_regular`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination](GraphCoverDomination.md)
