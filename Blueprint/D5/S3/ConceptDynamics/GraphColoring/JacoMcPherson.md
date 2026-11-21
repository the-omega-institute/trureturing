# The McPherson number of Jaco graphs

## Abstract

The McPherson number of the finite Jaco graph J_n(1) is b_n - 1, so it is nonrepetitive exactly when the outdegree b_n is.

**Definition 1.1 (A vertex explosion).**

$$(\operatorname{Adj}\left(\operatorname{explode}\left(H, w\right), a, b\right)) \Leftrightarrow ((\operatorname{Adj}\left(H, a, b\right)) \lor ((a \ne b) \land ((a = w) \lor (b = w))))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson.explode` (`✓ std3`).

*Citation.* Johan Kok; Susanth C (2014). *Introduction to the McPherson number, Upsilon(G) of a simple connected graph*. DOI: [10.48550/arXiv.1410.8637](https://doi.org/10.48550/arXiv.1410.8637). URL: <https://arxiv.org/abs/1410.8637v1>.

*Commentary.*

explode H w joins the exploding vertex w to every other vertex; arcs created by the explosion are recorded through the underlying graph only, since the McPherson number depends only on it.

**Definition 1.2 (The McPherson recursion).**

$$\operatorname{run}\left(G, L\right) = \operatorname{foldl}\left(explode, G, L\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson.run` (`✓ std3`).

*Citation.* Johan Kok; Susanth C (2014). *Introduction to the McPherson number, Upsilon(G) of a simple connected graph*. DOI: [10.48550/arXiv.1410.8637](https://doi.org/10.48550/arXiv.1410.8637). URL: <https://arxiv.org/abs/1410.8637v1>.

*Commentary.*

run G L lets the vertices of the list L explode in order, starting from G.

**Definition 1.3 (The McPherson number).**

$$\operatorname{Upsilon}\left(G\right) = \operatorname{min}\left(\{\operatorname{length}\left(L\right): \operatorname{run}\left(G, L\right) = K\}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson.mcpherson` (`✓ std3`).

*Citation.* Johan Kok; Susanth C (2014). *Introduction to the McPherson number, Upsilon(G) of a simple connected graph*. DOI: [10.48550/arXiv.1410.8637](https://doi.org/10.48550/arXiv.1410.8637). URL: <https://arxiv.org/abs/1410.8637v1>.

*Commentary.*

mcpherson G is the least length of an explosion list after which the underlying graph is complete (K is the complete graph on the vertices of G); this is the McPherson number of Kok and Susanth.

**Theorem 1.4 (The McPherson number of J_n(1)).**

$$(\forall L \in \operatorname{List}\left(V\right),\; (\operatorname{run}\left(G, L\right) = K) \Leftrightarrow (\operatorname{IsClique}\left(G, \{v: \operatorname{notMem}\left(v, L\right)\}\right))) \land ((\forall n \in \mathrm{Nat},\; \operatorname{Upsilon}\left(\operatorname{jaco}\left(n\right)\right) = \operatorname{b}\left(n\right) - 1) \land (\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow (((\operatorname{Upsilon}\left(\operatorname{jaco}\left(n - 1\right)\right) < \operatorname{Upsilon}\left(\operatorname{jaco}\left(n\right)\right)) \land (\operatorname{Upsilon}\left(\operatorname{jaco}\left(n\right)\right) < \operatorname{Upsilon}\left(\operatorname{jaco}\left(n + 1\right)\right))) \Leftrightarrow ((\operatorname{b}\left(n - 1\right) < \operatorname{b}\left(n\right)) \land (\operatorname{b}\left(n\right) < \operatorname{b}\left(n + 1\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Susanth C (2014). *Introduction to the McPherson number, Upsilon(G) of a simple connected graph*. DOI: [10.48550/arXiv.1410.8637](https://doi.org/10.48550/arXiv.1410.8637). URL: <https://arxiv.org/abs/1410.8637v1>.

*Commentary.*

After the explosions of L, two distinct vertices are adjacent exactly when they were adjacent in G or one of them exploded; hence the underlying graph is complete exactly when the non-exploding vertices form a clique of G, whatever the order of the explosions. For the finite Jaco graph J_n(1), with R_i=i+b_i and b_i=floor((i+1)/phi), JacoEndpointBeatty.beatty_threshold gives n<=R_i exactly when b_n<=i, so the labels at least b_n form a clique and the b_n-1 labels below b_n suffice. Conversely, a clique whose least label is m lies in [m,min(n,R_m)]: if m>=b_n it has at most n+1-b_n vertices, and if m<b_n it has at most b_m+1<=b_(b_n-1)+1<=n+1-b_n vertices, again by the threshold; so at least b_n-1 vertices must explode. Hence Upsilon(J_n(1))=b_n-1 for every n, including n=0,1,2, and since b_k>=1 for k>=1, Upsilon(J_(n-1)(1))<Upsilon(J_n(1))<Upsilon(J_(n+1)(1)) exactly when b_(n-1)<b_n<b_(n+1), for every n>=2. Theorem 2.3 of Kok and Susanth, arXiv:1410.8637v1, gives Upsilon(J_n(1)) as i-1 or i through the prime Jaconian vertex v_i for n>=3, and its page 5 conjectures the nonrepetition equivalence for n>=3; Kok, Linear Jaco Graphs: A Critical Review (2016), restates them as Theorem 2.48 and Conjecture 2.48.1 (not inspected), and Corollary 7 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124, derives Upsilon_n=b_n-1. The clique proof here is repo-derived.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson.explode`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson.mcpherson`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson.result`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson.run`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount](JacoDirectedPathCount.md)
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree](JacoMaximumDegree.md)
