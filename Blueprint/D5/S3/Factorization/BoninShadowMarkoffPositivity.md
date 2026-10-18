# Bonin's Shadow Markoff Positivity Region

## Abstract

The nonnegative integer shadow Markoff tree has exactly Bonin's quadrilateral of initial points.

A node is the rational tuple (a, al, b, be, c, ga), in that order. The real coordinates are a, b, c and the shadow coordinates are al, be, ga. All divisions below are rational divisions. Natural numbers include zero.

**Definition 1.1 (The two directions).**

$$\begin{aligned}\operatorname{inductive} Move: Type\\\mid \operatorname{Move}.\operatorname{l}: Move\\\mid \operatorname{Move}.\operatorname{r}: Move\end{aligned}$$

*Formalization.* `D5/S3/Factorization/BoninShadowMarkoffPositivity.Move` (`✓ std3`).

*Citation.* Nathan Bonin (2024). *Conditions of positivity on a shadow Markoff tree*. DOI: [10.48550/arXiv.2403.07668](https://doi.org/10.48550/arXiv.2403.07668). URL: <https://arxiv.org/abs/2403.07668>.

*Commentary.*

Section 5, page 9, uses the letters l and r. The constructor l mutates the second real-shadow pair, and r mutates the first pair.

**Definition 1.2 (A shadow mutation).**

$$\forall a \in \mathbb{Q}, al \in \mathbb{Q}, b \in \mathbb{Q}, be \in \mathbb{Q}, c \in \mathbb{Q}, ga \in \mathbb{Q},\; \begin{aligned}\operatorname{step}\left((a, al, b, be, c, ga), \operatorname{Move}.\operatorname{l}\right) = (a, al, c, ga, \frac{a^{2} + c^{2}}{b}, \frac{-\frac{a^{2} + c^{2}}{b} \cdot be + 2 \cdot a \cdot al + 2 \cdot c \cdot ga}{b})\\\operatorname{step}\left((a, al, b, be, c, ga), \operatorname{Move}.\operatorname{r}\right) = (c, ga, b, be, \frac{b^{2} + c^{2}}{a}, \frac{-\frac{b^{2} + c^{2}}{a} \cdot al + 2 \cdot b \cdot be + 2 \cdot c \cdot ga}{a})\end{aligned}$$

*Formalization.* `D5/S3/Factorization/BoninShadowMarkoffPositivity.step` (`✓ std3`).

*Citation.* Nathan Bonin (2024). *Conditions of positivity on a shadow Markoff tree*. DOI: [10.48550/arXiv.2403.07668](https://doi.org/10.48550/arXiv.2403.07668). URL: <https://arxiv.org/abs/2403.07668>.

*Commentary.*

These are the two cases of the mutation in the source's path code, Section 5, page 9. The first four entries keep the two unmutated pairs in their new order; the final pair contains the quadratic real mutation and its linear shadow.

**Definition 1.3 (Every finite branch, with the root).**

$$\forall al \in \mathbb{Q}, be \in \mathbb{Q}, ga \in \mathbb{Q},\; \forall C \in \operatorname{List}\left(Move\right),\; \operatorname{path}\left(al, be, ga, C\right) = \operatorname{List}.\operatorname{scanl}\left(step, (1, al, 1, be, 1, ga), \operatorname{Move}.\operatorname{r}::\operatorname{Move}.\operatorname{l}::C\right)$$

*Formalization.* `D5/S3/Factorization/BoninShadowMarkoffPositivity.path` (`✓ std3`).

*Citation.* Nathan Bonin (2024). *Conditions of positivity on a shadow Markoff tree*. DOI: [10.48550/arXiv.2403.07668](https://doi.org/10.48550/arXiv.2403.07668). URL: <https://arxiv.org/abs/2403.07668>.

*Commentary.*

Section 5, page 9: "the 2 mandatory beginning mutations (to the right, then to the left)". The initial real triple is (1,1,1). List.scanl includes its initial tuple, then the mandatory r and l moves, and then the word C.

**Definition 1.4 (All six entries are natural numbers).**

$$\forall t \in \mathbb{Q}\times\mathbb{Q}\times\mathbb{Q}\times\mathbb{Q}\times\mathbb{Q}\times\mathbb{Q},\; (\operatorname{IsNatNode}\left(t\right)) \Leftrightarrow (\exists a \in \mathbb{N}, al \in \mathbb{N}, b \in \mathbb{N}, be \in \mathbb{N}, c \in \mathbb{N}, ga \in \mathbb{N},\; t = ((a: \mathbb{Q}), (al: \mathbb{Q}), (b: \mathbb{Q}), (be: \mathbb{Q}), (c: \mathbb{Q}), (ga: \mathbb{Q})))$$

*Formalization.* `D5/S3/Factorization/BoninShadowMarkoffPositivity.IsNatNode` (`✓ std3`).

*Citation.* Nathan Bonin (2024). *Conditions of positivity on a shadow Markoff tree*. DOI: [10.48550/arXiv.2403.07668](https://doi.org/10.48550/arXiv.2403.07668). URL: <https://arxiv.org/abs/2403.07668>.

*Commentary.*

Equation (8), page 3: "a, b, c, α, β, γ ∈ ℕ." Each existential coordinate is explicitly cast to the rationals. In the tuple the real and shadow coordinates alternate, as in the source's path code.

**Definition 1.5 (The four projective vertices in an affine chart).**

$$\operatorname{quadrilateral} = \operatorname{convexHull}\left(\mathbb{Q}, \left\{(0, 0), (\frac{1}{2}, 0), (1, 1), (0, 2)\right\}\right)$$

*Formalization.* `D5/S3/Factorization/BoninShadowMarkoffPositivity.quadrilateral` (`✓ std3`).

*Citation.* Nathan Bonin (2024). *Conditions of positivity on a shadow Markoff tree*. DOI: [10.48550/arXiv.2403.07668](https://doi.org/10.48550/arXiv.2403.07668). URL: <https://arxiv.org/abs/2403.07668>.

*Commentary.*

Conjecture 1, page 3, gives the vertices {(0 : 0 : 1); (1/2 : 0 : 1) ≡ (1 : 0 : 2); (1 : 1 : 1); (0 : 2 : 1)}. In the chart ga = 1 their convex hull over the rationals has the four vertices displayed here.

**Definition 1.6 (Conjecture 1 for the rooted tree).**

$$(\operatorname{claim}) \Leftrightarrow (\forall al \in \mathbb{N}, be \in \mathbb{N}, ga \in \mathbb{N},\; ((al, be, ga) \ne (0, 0, 0)) \Rightarrow ((\forall C \in \operatorname{List}\left(Move\right),\; \forall t \in \mathbb{Q}\times\mathbb{Q}\times\mathbb{Q}\times\mathbb{Q}\times\mathbb{Q}\times\mathbb{Q},\; (t \in \operatorname{path}\left((al: \mathbb{Q}), (be: \mathbb{Q}), (ga: \mathbb{Q}), C\right)) \Rightarrow (\operatorname{IsNatNode}\left(t\right))) \Leftrightarrow ((0 < ga) \land ((\frac{(al: \mathbb{Q})}{(ga: \mathbb{Q})}, \frac{(be: \mathbb{Q})}{(ga: \mathbb{Q})}) \in \operatorname{quadrilateral}))))$$

*Formalization.* `D5/S3/Factorization/BoninShadowMarkoffPositivity.claim` (`✓ std3`).

*Citation.* Nathan Bonin (2024). *Conditions of positivity on a shadow Markoff tree*. DOI: [10.48550/arXiv.2403.07668](https://doi.org/10.48550/arXiv.2403.07668). URL: <https://arxiv.org/abs/2403.07668>.

*Commentary.*

Conjecture 1, page 3: "Every triple (A, B, C) of positive integer solutions to (3) can be obtained from the initial triple (7) where (α, β, γ) are positive integers such that (α : β : γ) ∈ ℚP² are the rational points that belong to the quadrilateral with vertices {(0 : 0 : 1); (1/2 : 0 : 1) ≡ (1 : 0 : 2); (1 : 1 : 1); (0 : 2 : 1)} depicted in the following figure via mutations (5) and permutations along the Markoff tree." The same page says: "It can be reformulated in terms of the initial triple (7) such that under every series of mutations along the Markoff tree the triple (α, β, γ) remain positive." The symbols al, be, ga encode α, β, γ. Equation (8) and the boundary vertices give the nonnegative integer reading. The zero triple is excluded; ga > 0 selects the affine chart. The tree is precisely the rooted tree of Sections 2 and 5, with every finite word after the mandatory r, l moves. Arbitrary independent permutations at the root are outside this assertion.

**Theorem 1.7 (The exact positivity region).**

$$\forall al \in \mathbb{N}, be \in \mathbb{N}, ga \in \mathbb{N},\; ((al, be, ga) \ne (0, 0, 0)) \Rightarrow ((\forall C \in \operatorname{List}\left(Move\right),\; \forall t \in \mathbb{Q}\times\mathbb{Q}\times\mathbb{Q}\times\mathbb{Q}\times\mathbb{Q}\times\mathbb{Q},\; (t \in \operatorname{path}\left((al: \mathbb{Q}), (be: \mathbb{Q}), (ga: \mathbb{Q}), C\right)) \Rightarrow (\operatorname{IsNatNode}\left(t\right))) \Leftrightarrow ((0 < ga) \land ((\frac{(al: \mathbb{Q})}{(ga: \mathbb{Q})}, \frac{(be: \mathbb{Q})}{(ga: \mathbb{Q})}) \in \operatorname{quadrilateral})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/BoninShadowMarkoffPositivity.result` (`✓ std3`). ∎

*Resolves.* `Problems/bonin-2024-shadow-markoff-positivity` (proved) by `D5/S3/Factorization/BoninShadowMarkoffPositivity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bonin-2024-shadow-markoff-positivity","declaration_gid":"D5/S3/Factorization/BoninShadowMarkoffPositivity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nathan Bonin (2024). *Conditions of positivity on a shadow Markoff tree*. DOI: [10.48550/arXiv.2403.07668](https://doi.org/10.48550/arXiv.2403.07668). URL: <https://arxiv.org/abs/2403.07668>.

*Commentary.*

The shifted shadows 3x − σa, with σ the sum of the initial shadows, satisfy a cone invariant under both mutations. This proves positivity throughout the tree when al + be ≤ 2ga and 2al ≤ be + ga. Conversely, the two constant direction spines satisfy forced second order recurrences. A negative forcing makes a shadow negative by the normalized Wronskian drift estimate. The two inequalities cut out exactly the displayed convex hull. Integrality is preserved even for arbitrary integer initial shadows. The result determines the polygon left unspecified by the source's Theorem 1 for this rooted tree.

## References

- Truth anchor: `D5/S3/Factorization/BoninShadowMarkoffPositivity.IsNatNode`
- Truth anchor: `D5/S3/Factorization/BoninShadowMarkoffPositivity.Move`
- Truth anchor: `D5/S3/Factorization/BoninShadowMarkoffPositivity.claim`
- Truth anchor: `D5/S3/Factorization/BoninShadowMarkoffPositivity.path`
- Truth anchor: `D5/S3/Factorization/BoninShadowMarkoffPositivity.quadrilateral`
- Truth anchor: `D5/S3/Factorization/BoninShadowMarkoffPositivity.result`
- Truth anchor: `D5/S3/Factorization/BoninShadowMarkoffPositivity.step`
- Dependency: [D5/S3/Factorization/MarkovEquationMutation](MarkovEquationMutation.md)
