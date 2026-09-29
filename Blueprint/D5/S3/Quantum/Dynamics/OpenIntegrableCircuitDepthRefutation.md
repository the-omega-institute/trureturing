# The conjectured minimum depths of open integrable circuits are false

## Abstract

Conjectures 1 and 2 of Garcia Fernandez, Paletta and Retore on the minimum depth of open-boundary integrable quantum circuits are false: with eight sites and two sites carrying -kappa the configuration (6, 3) runs in three layers, one fewer than conjectured, and with eleven sites the configuration (8, 4) runs in four, one fewer than conjectured.

**Definition 1.1 (Gates).**

$$\operatorname{sites}\left(N, \operatorname{U}\left(j\right)\right) = \left\{j, j + 1\right\},\quad\operatorname{sites}\left(N, K1\right) = \left\{1\right\},\quad\operatorname{sites}\left(N, KN\right) = \left\{N\right\}$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.sites` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The two-site gate U_j acts on the sites j and j + 1, the boundary gate K1 on site 1 and the boundary gate KN on site N.

**Definition 1.2 (The circuit of a configuration).**

$$\operatorname{circuit}\left(N, S\right) = KN, \operatorname{U}_{j} (j \in \{1, \operatorname{dots}, N - 1\} \setminus S, \operatorname{decreasing}), K1, \operatorname{U}_{n} (n \in S, \operatorname{increasing})\quad(\neg N \in S),\quad\operatorname{circuit}\left(N, S\right) = \operatorname{U}_{j} (j \in \{1, \operatorname{dots}, N - 1\} \setminus S, \operatorname{decreasing}), K1, \operatorname{U}_{n} (n \in S \setminus \left\{N\right\}, \operatorname{increasing}), KN\quad(N \in S)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.circuit` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The circuit of Theorems 1 and 2 for the set S of sites carrying -kappa, listed in time order, the rightmost factor of the operator product first. When N is not in S the boundary gate KN acts first, then U_j for the sites j < N outside S in decreasing order, then K1, then U_n for n in S in increasing order; when N is in S, KN acts last and U_N is omitted.

**Definition 1.3 (Layerings).**

$$\operatorname{RunsIn}\left(N, w, L\right) \Leftrightarrow (\exists f \in \mathbb{N} \to \mathbb{N},\; \left(\forall i \in \mathbb{N},\; (i < \operatorname{length}\left(w\right)) \Rightarrow (\operatorname{f}\left(i\right) < L)\right) \land \left(\forall j \in \mathbb{N},\; \forall i \in \mathbb{N},\; (\left(i < j \land j < \operatorname{length}\left(w\right)\right) \land \left(\exists k \in \mathbb{N},\; k \in \operatorname{sites}\left(N, \operatorname{w}\left(i\right)\right) \land k \in \operatorname{sites}\left(N, \operatorname{w}\left(j\right)\right)\right)) \Rightarrow (\operatorname{f}\left(i\right) < \operatorname{f}\left(j\right))\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.RunsIn` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

A list of gates fits in L layers when some layer map below L keeps the time order of every two gates that act on a common site in the chain of N sites; gates on disjoint sites may share a layer.

**Definition 1.4 (Depth).**

$$\operatorname{depth}\left(N, w\right) = \operatorname{inf} \{L \mid \operatorname{RunsIn}\left(N, w, L\right)\}$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.depth` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The least number of layers a circuit fits in.

**Definition 1.5 (Minimum depth).**

$$\operatorname{minDepth}\left(N, kappa\right) = \operatorname{inf} \{\operatorname{depth}\left(N, \operatorname{circuit}\left(N, S\right)\right) \mid S \subseteq \left\{1, \operatorname{dots}, N\right\}, \left|S\right| = kappa\}$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.minDepth` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The least depth over the configurations of kappa sites among 1, ..., N.

**Definition 1.6 (Conjecture 1).**

$$conjectureOne \Leftrightarrow (\forall N \in \mathbb{N},\; \forall kappa \in \mathbb{N},\; (\left(\operatorname{Odd}\left(N\right) \land 0 < kappa\right) \land kappa \le \left\lfloor\frac{N - 1}{2}\right\rfloor) \Rightarrow (\operatorname{minDepth}\left(N, kappa\right) = \left\lfloor\frac{N + 3}{2}\right\rfloor - kappa))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.conjectureOne` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

For odd N and 0 < kappa <= (N - 1)/2 the minimum depth is (N + 3)/2 - kappa.

**Definition 1.7 (Conjecture 2).**

$$conjectureTwo \Leftrightarrow (\forall N \in \mathbb{N},\; \forall kappa \in \mathbb{N},\; (\left(\operatorname{Even}\left(N\right) \land 0 < kappa\right) \land kappa \le \left\lfloor\frac{N}{2}\right\rfloor) \Rightarrow (\operatorname{minDepth}\left(N, kappa\right) = \left\lfloor\frac{N + 4}{2}\right\rfloor - kappa))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.conjectureTwo` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

For even N and 0 < kappa <= N/2 the minimum depth is (N + 4)/2 - kappa.

**Definition 1.8 (Either conjecture).**

$$claim \Leftrightarrow (conjectureOne \lor conjectureTwo)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.claim` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

At least one of the two conjectures holds; the result refutes both.

**Theorem 1.9 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/garcia-fernandez-2026-open-circuit-min-depth-refutation` (refuted) by `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"garcia-fernandez-2026-open-circuit-min-depth-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

For N = 8 and S = {3, 6} the circuit is KN, U7, U5, U4, U2, U1, K1, U3, U6 in time order, and the layers 0, 1, 0, 1, 0, 1, 2, 2, 2 keep the order of every two gates sharing a site, so its depth is at most 3 and the minimum depth for two sites is at most 3, while Conjecture 2 gives (8 + 4)/2 - 2 = 4. For N = 11 and S = {4, 8} the circuit is KN, U10, U9, U7, U6, U5, U3, U2, U1, K1, U4, U8 with the layers 0, 1, 2, 0, 1, 2, 0, 1, 2, 3, 3, 3, so the minimum depth for two sites is at most 4, while Conjecture 1 gives (11 + 3)/2 - 2 = 5. Both layer maps are checked by the kernel.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.RunsIn`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.circuit`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.conjectureOne`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.conjectureTwo`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.depth`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.minDepth`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.sites`
