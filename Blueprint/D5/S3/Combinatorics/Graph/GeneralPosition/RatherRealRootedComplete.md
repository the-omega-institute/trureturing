# Real-rooted general position polynomials

## Abstract

A finite nonempty connected graph has a real-rooted general position polynomial exactly when it is complete.

Vertices form a finite type V. General position uses IsGeneralPosition from CylinderSevenTen: no three distinct selected vertices satisfy the distance equality through the middle vertex. Distances are SimpleGraph.dist. On connected graphs these are shortest-path distances; no classification of disconnected graphs is asserted.

**Definition 1.1 (Counting general position sets).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (k : \mathrm{Nat}), \operatorname{alpha}\left(G, k\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left((\lambda (S : \operatorname{Finset}\left(V\right)) \mapsto \operatorname{Finset.card}\left(S\right) = k \land \operatorname{IsGeneralPosition}\left(G, S\right)), (\operatorname{Finset.univ} : \operatorname{Finset}\left(\operatorname{Finset}\left(V\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.alpha` (`✓ std3`).

*Citation.* B. A. Rather (2026). *Explicit Formulas and Unimodality Phenomena for General Position Polynomials*. DOI: [10.48550/arXiv.2603.06930](https://doi.org/10.48550/arXiv.2603.06930). URL: <https://arxiv.org/abs/2603.06930v3>.

*Commentary.*

Section 2, PDF page 4: “For each k ≥ 0, let α_k(G) denote the number of general position sets of size k.” Finset.univ ranges over all finite subsets of V; the filter requires both cardinality k and general position. Each subset is counted once.

**Definition 1.2 (The general position polynomial).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{psi}\left(G\right) = \sum_{k \in \operatorname{Finset.range}\left(\operatorname{Fintype.card}\left(V\right) + 1\right)} \operatorname{Polynomial.C}\left((\operatorname{alpha}\left(G, k\right) : \mathbb{Z})\right) \cdot \operatorname{Polynomial.X}^{k}$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.psi` (`✓ std3`).

*Citation.* B. A. Rather (2026). *Explicit Formulas and Unimodality Phenomena for General Position Polynomials*. DOI: [10.48550/arXiv.2603.06930](https://doi.org/10.48550/arXiv.2603.06930). URL: <https://arxiv.org/abs/2603.06930v3>.

*Commentary.*

Section 2, PDF page 4: “The general position polynomial of G is ψ(G) = ∑_{k≥0} α_k(G)x^k.” The indeterminate is Polynomial.X and coefficients are integers. The sum uses Finset.range (Fintype.card V + 1), since no subset has more than Fintype.card V vertices. Polynomial.C embeds the natural count after its cast to Int.

**Definition 1.3 (Only real complex zeros).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{IsRealRooted}\left(G\right) = (\forall (z : Complex), \operatorname{Polynomial.aeval}\left(z, \operatorname{psi}\left(G\right)\right) = 0 \Rightarrow \operatorname{Complex.im}\left(z\right) = 0)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.IsRealRooted` (`✓ std3`).

*Citation.* B. A. Rather (2026). *Explicit Formulas and Unimodality Phenomena for General Position Polynomials*. DOI: [10.48550/arXiv.2603.06930](https://doi.org/10.48550/arXiv.2603.06930). URL: <https://arxiv.org/abs/2603.06930v3>.

*Commentary.*

Section 8, item 1, PDF page 29: “For no nontrivial family is it currently known whether ψ(G) is always real-rooted.” Real-rooted means that every complex zero of psi G has zero imaginary part. Polynomial.aeval maps the integer coefficients into Complex.

**Definition 1.4 (The connected classification).**

$$claim = (\forall (V : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{Nonempty}\left(V\right) \Rightarrow \left(\operatorname{SimpleGraph.Connected}\left(G\right) \Rightarrow \left(\operatorname{IsRealRooted}\left(G\right) \Leftrightarrow G = \operatorname{Top.top}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* B. A. Rather (2026). *Explicit Formulas and Unimodality Phenomena for General Position Polynomials*. DOI: [10.48550/arXiv.2603.06930](https://doi.org/10.48550/arXiv.2603.06930). URL: <https://arxiv.org/abs/2603.06930v3>.

*Commentary.*

Section 8, item 1, PDF page 29: “For no nontrivial family is it currently known whether ψ(G) is always real-rooted. Even partial real-rootedness results for chordal graphs, bipartite graphs, or claw-free graphs (in analogy with [8, 13]) would be significant.” Section 1, PDF page 1: “All graphs considered are finite, simple and undirected.” The statement classifies all finite nonempty connected simple graphs: real-rootedness is equivalent to equality with the complete graph, SimpleGraph top.

**Theorem 1.5 (Real-rootedness is equivalent to completeness).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{Nonempty}\left(V\right) \Rightarrow \left(\operatorname{SimpleGraph.Connected}\left(G\right) \Rightarrow \left(\operatorname{IsRealRooted}\left(G\right) \Leftrightarrow G = \operatorname{Top.top}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.result` (`✓ std3`). ∎

*Resolves.* `Problems/rather-2026-general-position-real-rooted-complete` (proved) by `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rather-2026-general-position-real-rooted-complete","declaration_gid":"D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* B. A. Rather (2026). *Explicit Formulas and Unimodality Phenomena for General Position Polynomials*. DOI: [10.48550/arXiv.2603.06930](https://doi.org/10.48550/arXiv.2603.06930). URL: <https://arxiv.org/abs/2603.06930v3>.

*Commentary.*

Every subset with at most two vertices is in general position, so the first three coefficients are 1, n and choose(n,2), where n is the vertex count. Reflecting the polynomial at n gives a monic real-split polynomial. If zero were a root, removing it would preserve the first two elementary symmetric functions on only n−1 roots, contradicting Newton's inequality. Thus the full vertex set is in general position. In a connected noncomplete graph a shortest path contains a distance-two triple, which contradicts that property. Conversely, all subsets of a complete graph are in general position, giving psi top = (1 + Polynomial.X)^n and only the zero −1.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.IsRealRooted`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.alpha`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.psi`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.result`
- Dependency: [D5/S3/Analytic/RealRootedCoefficientNewton](../../../Analytic/RealRootedCoefficientNewton.md)
- Dependency: [D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen](CylinderSevenTen.md)
