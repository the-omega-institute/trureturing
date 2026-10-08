# A 23-edge coupling realizes the ten-mode Fourier transform

## Abstract

Barriga et al. (arXiv:2609.05644) realize the discrete Fourier transform F_N with one waveguide array, Phi_out exp(-i H) Phi_in = F_N, and conjecture edge ranges for the coupling graphs; for N = 10 their third conjecture, with l = 5, requires at least 25 edges. A connected real symmetric coupling matrix with nonnegative couplings and 23 edges realizes F_10 exactly, so the bound fails.

**Definition 1.1 (The ten-mode Fourier transform).**

$$\forall x \in \operatorname{Fin}\left(10\right),\; \forall y \in \operatorname{Fin}\left(10\right),\; \operatorname{F10}\left(x, y\right) = \operatorname{exp}\left(-2\pi i x y / 10\right) / \operatorname{sqrt}\left(10\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.F10` (`✓ std3`).

*Citation.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

The discrete Fourier transform on ten modes, with entries exp(-2 pi i x y / 10) / sqrt 10 for x, y in Fin 10, the paper's F_N with omega = exp(-2 i pi / N).

**Definition 1.2 (Number of edges).**

$$\forall H \in \operatorname{Matrix}\left(\operatorname{Fin}\left(10\right), \operatorname{Fin}\left(10\right), \mathbb{R}\right),\; \operatorname{edgeCount}\left(H\right) = \operatorname{card}\left(\operatorname{filter}\left((x, y) \mapsto x < y \land H\left(x, y\right) \ne 0, \operatorname{univ}\left(\operatorname{Fin}\left(10\right) \times \operatorname{Fin}\left(10\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.edgeCount` (`✓ std3`).

*Citation.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

The number of unordered pairs x < y of modes with a nonzero coupling H x y: the edges of the coupling graph, whose vertices are the waveguides.

**Definition 1.3 (The coupling graph).**

$$\forall H \in \operatorname{Matrix}\left(\operatorname{Fin}\left(10\right), \operatorname{Fin}\left(10\right), \mathbb{R}\right),\; \forall x \in \operatorname{Fin}\left(10\right),\; \forall y \in \operatorname{Fin}\left(10\right),\; \operatorname{Adj}\left(\operatorname{supportGraph}\left(H\right), x, y\right) \Leftrightarrow (x \ne y \land \left(H\left(x, y\right) \ne 0 \lor H\left(y, x\right) \ne 0\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.supportGraph` (`✓ std3`).

*Citation.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

The simple graph on Fin 10 in which distinct modes x and y are adjacent when H x y or H y x is nonzero.

**Definition 1.4 (Phase shifters).**

$$\forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(10\right), \operatorname{Fin}\left(10\right), \mathbb{C}\right),\; \operatorname{IsUnimodularDiagonal}\left(Phi\right) \Leftrightarrow (\exists z \in \operatorname{Fin}\left(10\right) \to \mathbb{C},\; \left(\forall x \in \operatorname{Fin}\left(10\right),\; |z\left(x\right)| = 1\right) \land Phi = \operatorname{diagonal}\left(z\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.IsUnimodularDiagonal` (`✓ std3`).

*Citation.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

A diagonal matrix whose diagonal entries are complex numbers of modulus 1, the input and output phase shifters of the paper.

**Definition 1.5 (The conjectured bound for N = 10).**

$$claim \Leftrightarrow (\forall H \in \operatorname{Matrix}\left(\operatorname{Fin}\left(10\right), \operatorname{Fin}\left(10\right), \mathbb{R}\right),\; \operatorname{IsSymm}\left(H\right) \Rightarrow (\left(\forall x \in \operatorname{Fin}\left(10\right),\; \forall y \in \operatorname{Fin}\left(10\right),\; x \ne y \Rightarrow (0 \le H\left(x, y\right))\right) \Rightarrow (\operatorname{Connected}\left(\operatorname{supportGraph}\left(H\right)\right) \Rightarrow (\left(\exists Q \in \operatorname{Matrix}\left(\operatorname{Fin}\left(10\right), \operatorname{Fin}\left(10\right), \mathbb{C}\right),\; \exists R \in \operatorname{Matrix}\left(\operatorname{Fin}\left(10\right), \operatorname{Fin}\left(10\right), \mathbb{C}\right),\; \left(\operatorname{IsUnimodularDiagonal}\left(Q\right) \land \operatorname{IsUnimodularDiagonal}\left(R\right)\right) \land Q \cdot \operatorname{hamiltonianPropagator}\left(\operatorname{map}\left(H, \operatorname{ofReal}\right), 1\right) \cdot R = \operatorname{F10}\right) \Rightarrow (25 \le \operatorname{edgeCount}\left(H\right))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.claim` (`✓ std3`).

*Citation.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

The third conjecture of the paper for N = 10 with l = 5, read for the most restrictive notion of solution: every real symmetric coupling matrix with nonnegative off-diagonal entries and connected coupling graph whose propagator exp(-i H) gives F10 after input and output phase shifters has at least 25 edges. The propagator is the frozen hamiltonianPropagator at time 1, applied to the complex matrix map(H, ofReal) obtained by casting each real entry of H to a complex number.

**Theorem 1.6 (The bound fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/barriga-2026-dft-ten-mode-edge-bound` (refuted) by `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"barriga-2026-dft-ten-mode-edge-bound","declaration_gid":"D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

Let s = sqrt 5 and let C0 be the symmetric circulant on Z_5 with a = pi (35 - 13 s)/25 at distance 1 and b = pi (35 + 13 s)/25 at distance 2. Its Fourier eigenvalues are 28 pi/5, -4 pi, 6 pi/5, 6 pi/5 and -4 pi, so exp(-i C0) has entries (w/sqrt 5) w^(4 (j - k)^2) with w = exp(2 pi i/5). With q = (21 s - 65)/20 and g = q + i sqrt(1 - q^2), the matrix P with entries (Re(g w^(j + k - 1)) + cos(2 pi (j - k)/5))/5 is a rank-one projector onto a vector of the -4 pi eigenspace. Hence K = C0 + 2 pi P commutes with C0 and exp(-i K) = exp(-i C0) exp(-2 pi i P) = exp(-i C0). The value of q makes K 0 1 = 0, and every other off-diagonal entry of K is positive. Through x -> (x mod 2, x mod 5) the ten-mode matrix is H = (pi/4) X (x) I + I (x) K. Its exponential is w D F10 D for the unimodular diagonal D with entries (-i)^(x mod 2) w^(4 (x mod 5)^2), by the congruence 5ab + 4jk = -xy mod 10. The coupling graph consists of the cliques on the even and on the odd modes without the edges {0, 6} and {1, 5}, together with the five edges {x, x + 5}. It is connected and has 23 < 25 edges.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.F10`
- Truth anchor: `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.IsUnimodularDiagonal`
- Truth anchor: `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.edgeCount`
- Truth anchor: `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.supportGraph`
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
