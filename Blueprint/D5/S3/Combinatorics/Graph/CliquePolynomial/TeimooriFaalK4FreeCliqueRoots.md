# A K4-free graph with a nonreal clique-polynomial root

## Abstract

A connected graph on seven vertices contains no four-vertex clique, but its clique polynomial has a nonreal complex zero.

**Definition 1.1 (Teimoori Faal's Conjecture 4.1).**

$$claim \Leftrightarrow (\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(G.Adj\right)] (\operatorname{SimpleGraph.Connected}\left(G\right)) \Rightarrow ((\operatorname{SimpleGraph.CliqueFree}\left(G, 4\right)) \Rightarrow (\forall (z : \mathbb{C}), (\operatorname{Polynomial.aeval}\left(z, \operatorname{D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots.cliquePoly}\left(G\right)\right) = 0) \Rightarrow (\operatorname{Complex.im}\left(z\right) = 0))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots.claim` (`✓ std3`).

*Citation.* Hossein Teimoori Faal (2021). *Sums of Polynomials and Clique Roots*. DOI: [10.48550/arXiv.2112.09744](https://doi.org/10.48550/arXiv.2112.09744). URL: <https://arxiv.org/abs/2112.09744v1>.

*Commentary.*

Conjecture 4.1, page 5: "Let G be a connected K₄-free graphs, then G has only clique roots." Section 2, page 3, says: "The real root of the clique polynomial of G is called the clique root of G." Thus every complex zero must have imaginary part zero. The vertex type V is finite, equality and adjacency are decidable, connectedness is SimpleGraph.Connected, and K₄ exclusion is SimpleGraph.CliqueFree 4. The integer polynomial is the existing D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots.cliquePoly: its coefficient of X to the power k counts k-element vertex subsets forming a clique, with the empty clique counted once. It sums from zero through Fintype.card V; coefficients above the largest clique size vanish. Polynomial.aeval evaluates this integer polynomial in ℂ.

**Theorem 1.2 (A seven-vertex refutation).**

$$\neg (\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(G.Adj\right)] (\operatorname{SimpleGraph.Connected}\left(G\right)) \Rightarrow ((\operatorname{SimpleGraph.CliqueFree}\left(G, 4\right)) \Rightarrow (\forall (z : \mathbb{C}), (\operatorname{Polynomial.aeval}\left(z, \operatorname{D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots.cliquePoly}\left(G\right)\right) = 0) \Rightarrow (\operatorname{Complex.im}\left(z\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots.result` (`✓ std3`). ∎

*Resolves.* `Problems/tf2112` (refuted) by `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tf2112","declaration_gid":"D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hossein Teimoori Faal (2021). *Sums of Polynomials and Clique Roots*. DOI: [10.48550/arXiv.2112.09744](https://doi.org/10.48550/arXiv.2112.09744). URL: <https://arxiv.org/abs/2112.09744v1>.

*Commentary.*

On the vertices 0 through 6, take the undirected edges {0,3}, {0,4}, {0,5}, {0,6}, {1,3}, {1,4}, {1,5}, {1,6}, {2,3}, {2,5}, {3,4}, {3,5}, {4,6}, and {5,6}. The path [0,3,1,4,6,5,2] visits every vertex, proving connectedness. There is no four-vertex clique. The clique counts are 1, 7, 14, and 9 in sizes zero through three, followed by zeros. The clique polynomial is therefore 1+7X+14X²+9X³. Its cubic discriminant is −31. If it split over ℝ, the discriminant would be a square of a real product of root differences and hence nonnegative. Algebraic closure of ℂ then gives a complex zero outside the image of ℝ. This contradicts the assertion that all complex zeros have imaginary part zero. The theorem concerns this finite graph; it makes no assertion about a uniform family or vertex connectivity beyond connectedness.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots.result`
- Dependency: [D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots](TeimooriFaalFlatCliqueRoots.md)
