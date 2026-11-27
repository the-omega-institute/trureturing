# Normalized-Laplacian cospectrality of closed-neighborhood coronas

## Abstract

Adjacency-cospectral regular factors give normalized-Laplacian cospectral closed-neighborhood coronas in both orders.

**Theorem 1.1 (Question 5.21 holds in both factor orders).**

$$\begin{aligned}&\forall V,Z,W: Type, [\operatorname{Fintype}\left(V\right)][\operatorname{Fintype}\left(Z\right)][\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(V\right)][\operatorname{DecidableEq}\left(Z\right)][\operatorname{DecidableEq}\left(W\right)],\\&\quad\forall G_{1}: \operatorname{SimpleGraph}\left(V\right), G_{2}: \operatorname{SimpleGraph}\left(Z\right), H: \operatorname{SimpleGraph}\left(W\right), [\operatorname{DecidableRel}\left(G_{1}.Adj\right)][\operatorname{DecidableRel}\left(G_{2}.Adj\right)][\operatorname{DecidableRel}\left(H.Adj\right)],\\&\quad\forall d_{1},d_{2}: \mathbb{N}, \operatorname{IsRegularOfDegree}\left(G_{1}, d_{1}\right) \Rightarrow \operatorname{IsRegularOfDegree}\left(G_{2}, d_{2}\right) \Rightarrow\\&\quad\operatorname{charpoly}\left(\operatorname{A}\left(G_{1}\right)\right) = \operatorname{charpoly}\left(\operatorname{A}\left(G_{2}\right)\right) \Rightarrow\\&\quad(\operatorname{charpoly}\left(\operatorname{L}\left(\operatorname{corona}\left(G_{1}, H\right)\right)\right) = \operatorname{charpoly}\left(\operatorname{L}\left(\operatorname{corona}\left(G_{2}, H\right)\right)\right)) \land (\operatorname{charpoly}\left(\operatorname{L}\left(\operatorname{corona}\left(H, G_{1}\right)\right)\right) = \operatorname{charpoly}\left(\operatorname{L}\left(\operatorname{corona}\left(H, G_{2}\right)\right)\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian.normalized_laplacian_charpoly_corona` (`✓ std3`). ∎

*Resolves.* `Problems/sason-et-al-2025-corona-normalized-laplacian-question-5-21` (proved) by `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian.normalized_laplacian_charpoly_corona`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sason-et-al-2025-corona-normalized-laplacian-question-5-21","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian.normalized_laplacian_charpoly_corona","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Igal Sason; Noam Krupnik; Suleiman Hamud; Abraham Berman (2025). *On Spectral Graph Determination*. DOI: [10.3390/math13040549](https://doi.org/10.3390/math13040549). URL: <https://arxiv.org/abs/2412.20775v6>.

*Commentary.*

The vertex types are independently finite. The function A assigns the real adjacency matrix and L assigns the real normalized Laplacian. The latter is the ordinary Laplacian scaled on both sides by the diagonal inverse square-root degree, with scale zero at degree zero. The corona attaches one copy of its second graph to the closed neighborhood of each vertex of its first graph.

The adjacency characteristic polynomial determines the vertex count. After relabeling, spectral conjugacy followed by a reflection in the common row-sum eigenspace gives an orthogonal intertwiner U that fixes the constant vector. When the regular graph is the base, U acts on the base and on the index of each copy. When the regular graph is attached, U acts within each copy and the base is fixed.

In both orders the lifted intertwiner has nonzero entries only between vertices of equal degree, so it also intertwines the degree diagonal and inverse square-root diagonal. Orthogonal similarity gives equality of characteristic polynomials. The proof imposes no connectedness or positive-degree condition.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian.normalized_laplacian_charpoly_corona`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks](Blocks.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/RegularIntertwiner](RegularIntertwiner.md)
