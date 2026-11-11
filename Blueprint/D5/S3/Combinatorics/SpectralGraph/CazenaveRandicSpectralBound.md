# Cazenave's adjacency–Randić–Laplacian inequality

## Abstract

Connected graphs satisfy the Randic plus second-Laplacian spectral bound.

**Definition 1.1 (Ordered adjacency eigenvalues).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left((G).\operatorname{Adj}\right)] \forall i \in \operatorname{Fin}\left(n\right),\; \forall h \in ((G).\operatorname{adjMatrix}\left(\mathrm{Real}\right)).\operatorname{IsHermitian},\; \forall e \in (n = \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Fin}\left(n\right)\right)),\; \operatorname{adjEig}\left(G, i\right) = h.\operatorname{eigenvalues}_{0}\left(\operatorname{Fin}.\operatorname{cast}\left(e, i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.adjEig` (`✓ std3`).

*Citation.* Tristan Cazenave (2026). *Lemmas and Conjectures in Spectral Graph Theory*. URL: <https://arxiv.org/abs/2611.03879v1>.

*Commentary.*

Page 1 states: “A is the adjacency matrix, with eigenvalues λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ (counted with multiplicity) and rank rk(A).” The index i is zero based. The formula uses the ordinary adjacency matrix over Real and the decreasing eigenvalues₀. Here h is any proof that this matrix is Hermitian and e is any proof of the indicated cardinality equality; proof irrelevance identifies them with the proofs in the definition.

**Definition 1.2 (The Randić index).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left((G).\operatorname{Adj}\right)] \forall s \in (\forall u \in \operatorname{Fin}\left(n\right),\; \forall v \in \operatorname{Fin}\left(n\right),\; \frac{1}{\operatorname{Real}.\operatorname{sqrt}\left((((G).\operatorname{degree}\left(u\right) : \mathrm{Real}) \cdot ((G).\operatorname{degree}\left(v\right) : \mathrm{Real}))\right)} = \frac{1}{\operatorname{Real}.\operatorname{sqrt}\left((((G).\operatorname{degree}\left(v\right) : \mathrm{Real}) \cdot ((G).\operatorname{degree}\left(u\right) : \mathrm{Real}))\right)}),\; \operatorname{randic}\left(G\right) = \sum_{e \in (G).\operatorname{edgeFinset}} \operatorname{Sym2}.\operatorname{lift}\left(\langle(\lambda (u v : \operatorname{Fin}\left(n\right)) \mapsto \frac{1}{\operatorname{Real}.\operatorname{sqrt}\left((((G).\operatorname{degree}\left(u\right) : \mathrm{Real}) \cdot ((G).\operatorname{degree}\left(v\right) : \mathrm{Real}))\right)}), s\rangle, e\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.randic` (`✓ std3`).

*Citation.* Tristan Cazenave (2026). *Lemmas and Conjectures in Spectral Graph Theory*. URL: <https://arxiv.org/abs/2611.03879v1>.

*Commentary.*

Page 1 states: “R = ∑ᵤᵥ∈E (dᵤdᵥ)⁻¹ᐟ² is the Randić index.” The finite sum ranges over G.edgeFinset, so each unordered edge occurs once. Sym2.lift applies the symmetric reciprocal-square-root function to an unordered pair. The formula displays any symmetry proof s; proof irrelevance identifies it with the proof in the definition. Degrees are coerced from Nat to Real, and Real.sqrt is the nonnegative square root. Both endpoints of an edge have positive degree.

**Definition 1.3 (Conjecture 4 (#112951)).**

$$\operatorname{claim} = (\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n+2\right)\right),\; [\operatorname{DecidableRel}\left((G).\operatorname{Adj}\right)] (G).\operatorname{Connected} \Rightarrow \operatorname{adjEig}\left(G, 0\right) \le \operatorname{randic}\left(G\right)+\operatorname{LinWangCaiBroomSpectralRatio}.\operatorname{lapEig}\left(G, 1\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.claim` (`✓ std3`).

*Citation.* Tristan Cazenave (2026). *Lemmas and Conjectures in Spectral Graph Theory*. URL: <https://arxiv.org/abs/2611.03879v1>.

*Commentary.*

Page 11 states: “Conjecture 4 (#112951). λ₁ ≤ R + µ₂.” Page 1 states: “All graphs are simple, undirected and connected, with n ≥ 2 vertices and m edges.” SimpleGraph supplies undirectedness and absence of loops. The parameter n in this formula is graph order minus two. The anonymous bracket supplies decidable adjacency. The ordinary Laplacian is D − A; LinWangCaiBroomSpectralRatio.lapEig G 1 is its second-largest eigenvalue, counted with multiplicity. At order two it is the smaller Laplacian eigenvalue.

**Theorem 1.4 (The spectral inequality).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n+2\right)\right),\; [\operatorname{DecidableRel}\left((G).\operatorname{Adj}\right)] (G).\operatorname{Connected} \Rightarrow \operatorname{adjEig}\left(G, 0\right) \le \operatorname{randic}\left(G\right)+\operatorname{LinWangCaiBroomSpectralRatio}.\operatorname{lapEig}\left(G, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-cazenave2611c4` (proved) by `D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-cazenave2611c4","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tristan Cazenave (2026). *Lemmas and Conjectures in Spectral Graph Theory*. URL: <https://arxiv.org/abs/2611.03879v1>.

*Commentary.*

Choose u of maximum degree Δ and v of largest degree among the remaining vertices; write r = √Δ and d = degree(v). Connectedness gives Δ ≥ d ≥ 1. Edge charging gives r ≤ randic G. The positive vector taking value r at u and value one elsewhere satisfies A h ≤ (r + d − 1) h, so adjEig G 0 ≤ r + d − 1. A nonzero vector supported on u and v and orthogonal to the first Laplacian eigenvector has Rayleigh quotient at least d − 1. Expansion in the decreasing orthonormal spectral basis bounds that quotient above by lapEig G 1. The three estimates on this same graph give the displayed inequality.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.adjEig`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.randic`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.result`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio](LinWangCaiBroomSpectralRatio.md)
