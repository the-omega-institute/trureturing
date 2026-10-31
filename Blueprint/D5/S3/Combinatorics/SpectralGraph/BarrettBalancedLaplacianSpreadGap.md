# The balanced-digraph Laplacian-spread gap

## Abstract

A balanced loopless unweighted digraph has no Laplacian spread strictly between zero and one.

**Definition 1.1 (Conjecture 14).**

$$\operatorname{claim} \Leftrightarrow (\forall n \in \mathbb{N},\; 2 \le n \Rightarrow \left(\forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \neg (\operatorname{Digraph}.\operatorname{Adj}\left(G, i, i\right))\right) \Rightarrow \left(\operatorname{BarrettLaplacianSpreadSlopeRefutation}.\operatorname{Balanced}\left(G\right) \Rightarrow \neg (0 < \operatorname{BarrettLaplacianSpreadSlopeRefutation}.\operatorname{spread}\left(G\right) \land \operatorname{BarrettLaplacianSpreadSlopeRefutation}.\operatorname{spread}\left(G\right) < 1)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap.claim` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Conjecture 14, page 15: "There is no balanced digraph that satisfies 0<sp(Γ)<1." Section 6 states: "Note that all conjectures are made for unweighted digraphs." The quantifiers cover every order n≥2 and every loopless directed relation on Fin n. Opposite arcs are allowed. Balanced and spread are the shared directed-degree and quadratic-extremum definitions.

**Theorem 1.2 (Conjecture 14 is true).**

$$\forall n \in \mathbb{N},\; 2 \le n \Rightarrow \left(\forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \neg (\operatorname{Digraph}.\operatorname{Adj}\left(G, i, i\right))\right) \Rightarrow \left(\operatorname{BarrettLaplacianSpreadSlopeRefutation}.\operatorname{Balanced}\left(G\right) \Rightarrow \neg (0 < \operatorname{BarrettLaplacianSpreadSlopeRefutation}.\operatorname{spread}\left(G\right) \land \operatorname{BarrettLaplacianSpreadSlopeRefutation}.\operatorname{spread}\left(G\right) < 1)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/bce14` (proved) by `D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bce14","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Projected coordinate vectors give Rayleigh values ndᵢ/(n−1). Integral degrees therefore coincide whenever the spread is at most one. The symmetric adjacency matrix has entries 0, 1, or 2. A width below one reduces it, or its complement, to an even-regular simple graph. At interior degrees the centered Frobenius estimate contradicts that width. The matching endpoint gives Rayleigh values −1 and 1, and the empty and complete endpoints have scalar restrictions and zero spread. This proves the entire quantified gap assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap.result`
- Dependency: [D5/S1/Dynamics/Symbolic/FiniteGraphEntropy](../../../S1/Dynamics/Symbolic/FiniteGraphEntropy.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation](BarrettLaplacianSpreadSlopeRefutation.md)
