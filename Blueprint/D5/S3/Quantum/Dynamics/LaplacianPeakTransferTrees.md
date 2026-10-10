# Infinitely many non-star trees admit Laplacian peak state transfer

## Abstract

There are arbitrarily large non-star trees with Laplacian peak state transfer. For each positive odd s, join a root to s(s+1)+1 hubs and each hub to s(s+1) leaves. Transfer from the root to every hub attains the spectral entry bound at time pi.

**Definition 1.1 (Laplacian spectral idempotents).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall (theta : \mathbb{R}), \operatorname{lapIdempotent}\left(G, theta\right) = \operatorname{let} hL = G.\operatorname{isHermitian_{lapMatrix}}\left(\mathbb{R}\right); \sum_{i: \operatorname{Fin}\left(n\right), hL.\operatorname{eigenvalues}\left(i\right) = theta} \operatorname{vecMulVec}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(hL.\operatorname{eigenvectorBasis}\left(i\right)\right), \operatorname{WithLp}.\operatorname{ofLp}\left(hL.\operatorname{eigenvectorBasis}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.lapIdempotent` (`✓ std3`).

*Citation.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Section 3, p. 5: "E_r is the idempotent projection onto the θ_r-eigenspace." The source writes M as the sum of θ_r E_r over its distinct eigenvalues. Here M is G.lapMatrix over the reals. The formula sums the outer products of the real orthonormal eigenbasis vectors whose eigenvalue equals theta; a missing eigenvalue gives the zero matrix. hL denotes G.isHermitian_lapMatrix over the reals.

**Definition 1.2 (An entry of the bounding matrix).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall (v : \operatorname{Fin}\left(n\right)), \forall (u : \operatorname{Fin}\left(n\right)), \operatorname{boundingEntry}\left(G, v, u\right) = \operatorname{let} hL = G.\operatorname{isHermitian_{lapMatrix}}\left(\mathbb{R}\right); \sum_{theta \in \operatorname{Finset}.\operatorname{image}\left(hL.\operatorname{eigenvalues}, \operatorname{univ}\right)} \left|\operatorname{lapIdempotent}\left(G, theta, v, u\right)\right|$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.boundingEntry` (`✓ std3`).

*Citation.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Section 3, p. 5: "We will refer to B(M) := ∑_{r=0}^d |(E_r)| as the bounding matrix of M, as the (v,u)-entry of B(M) upper-bounds |U(t)_{v,u}| for all values of t." Absolute values are entrywise. The finite image of hL.eigenvalues counts each distinct eigenvalue once. The two arguments v,u specify the (v,u)-entry, and hL is G.isHermitian_lapMatrix over the reals.

**Definition 1.3 (The Laplacian propagator).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall (tau : \mathbb{R}), \operatorname{lapPropagator}\left(G, tau\right) = \operatorname{ProjectionProbabilityFlow}.\operatorname{hamiltonianPropagator}\left(\operatorname{Matrix}.\operatorname{map}\left(G.\operatorname{lapMatrix}\left(\mathbb{R}\right), \operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right), -tau\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.lapPropagator` (`✓ std3`).

*Citation.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Section 3, p. 5: "In particular, the transition matrix of the continuous-time quantum walk on M can be written as the following matrix-valued function in time:" U(t) = e^{itM} = ∑_{r=0}^d e^{itθ_r} E_r. For Laplacian dynamics M is G.lapMatrix over the reals, mapped entrywise into the complex numbers by algebraMap. ProjectionProbabilityFlow.hamiltonianPropagator at time -tau equals exp(i tau L), the source's propagator.

**Definition 1.4 (Peak state transfer).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall (u : \operatorname{Fin}\left(n\right)), \forall (v : \operatorname{Fin}\left(n\right)), \operatorname{PeakTransfer}\left(G, u, v\right) \Leftrightarrow ((u \ne v) \land (\exists (tau : \mathbb{R}), \left\lVert \operatorname{lapPropagator}\left(G, tau, v, u\right) \right\rVert = \operatorname{boundingEntry}\left(G, v, u\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.PeakTransfer` (`✓ std3`).

*Citation.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Section 3, p. 5: "For distinct vertices u,v, we say that there is peak state transfer from u to v with respect to M if there exists a time τ such that |U(τ)_{v,u}| = B(M)_{v,u}." Here tau encodes τ, M is the real Laplacian, and the complex norm is its absolute value. The equality is at the (v,u)-entry, so u is the input vertex.

**Definition 1.5 (Open Problem 7.1).**

$$claim \Leftrightarrow (\forall (N : \mathbb{N}), \exists (n : \mathbb{N}), (n \ge N) \land (\exists (T : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (T.\operatorname{IsTree}) \land ((\forall (m : \mathbb{N}), \operatorname{IsEmpty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(T, \operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(1\right), \operatorname{Fin}\left(m\right)\right)\right)\right)) \land (\exists (u : \operatorname{Fin}\left(n\right)), \exists (v : \operatorname{Fin}\left(n\right)), \operatorname{PeakTransfer}\left(T, u, v\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.claim` (`✓ std3`).

*Citation.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Section 7, p. 21: "Determine whether infinitely many such trees, not isomorphic to the star graph, admit Laplacian peak state transfer." Figure 10, p. 22, shows two stars and the 10-vertex rooted tree with three hubs and two leaves per hub. In the formula N ranges over natural lower bounds on the number n of vertices, T is a simple graph on Fin n, and IsTree means connected and acyclic. The exclusion covers every star K_(1,m), including m=0, through the absence of a SimpleGraph.Iso to completeBipartiteGraph (Fin 1) (Fin m). The PeakTransfer instances use classical adjacency decidability. Arbitrarily large finite orders imply infinitely many isomorphism classes.

**Theorem 1.6 (The answer is affirmative).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.result` (`✓ std3`). ∎

*Resolves.* `Problems/coutinho-guo-schmeits-2025-laplacian-peak-transfer-trees` (proved) by `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"coutinho-guo-schmeits-2025-laplacian-peak-transfer-trees","declaration_gid":"D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Put l=s(s+1), k=l+1 and n=1+k(l+1), with s positive and odd. The root, hubs and leaves give a subspace of cell-constant vectors preserved by the Laplacian. The root basis vector decomposes into eigenvectors with eigenvalues 0, s^2+1 and (s+1)^2+1. Their root-to-hub spectral entries have signs positive, positive and negative. At time pi the corresponding phases are 1, 1 and -1, so the absolute value of the propagator entry equals the sum of the absolute spectral entries. This is the phase-alignment mechanism of Lemma 5.2. Each graph is connected and has n-1 edges. The root and a hub both have degree at least two, which excludes all stars. Taking s=2N+1 yields a graph whose order is at least N. The resulting transfer is across one edge.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.PeakTransfer`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.boundingEntry`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.lapIdempotent`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.lapPropagator`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.result`
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Dynamics/RationalWeightPathTransfer](RationalWeightPathTransfer.md)
