---
bibkey: benedito2025visualizing
authors: A. Benedito; G. Sierra
year: 2025
title: "Visualizing Three-Qubit Entanglement"
doi: null
url: https://arxiv.org/abs/2505.23638v2
claim: "The authors state the canonical five-term decomposition, the Bloch-norm coordinates of the one-qubit reduced states, the tangle tau(psi) = 4 |Hdet(t_ijk)| = 4 lambda_0^2 lambda_4^2, and conjecture a geometric ansatz for normalized GHZ states excluding type 5."
strata_touched:
  - D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation
license: citation-only
triage: anchor
---

# Visualizing Three-Qubit Entanglement

A. Benedito and G. Sierra, *Visualizing Three-Qubit Entanglement*, arXiv:2505.23638v2 (2025), published as *Entropy* 27(8), 800. The canonical coefficient tensor, finite-sum one-qubit partial traces, Pauli-coordinate Bloch lengths, full type-5 classification and Cayley three-tangle define the quantities in the geometric ansatz.

The paper prints the canonical decomposition (arXiv v2, p. 3, Eqs. (3)--(4)):

> “$\ket{\psi} \overset{\text{CD}}{\rightarrow} \ket{\lambda_0, \vec{\lambda}, \lambda_4; \varphi} := \Big[ \lambda_0 \ket{000} + \lambda_1 e^{i \varphi} \ket{100} + \lambda_2 \ket{101} + \lambda_3 \ket{110} + \lambda_4 \ket{111} \Big]$ where $\lambda_j \in [0,1] \forall j; \sum_{j=0}^4 \lambda_j^2 = 1; \varphi \in [0,\pi]$.”

For a one-qubit reduced state it writes $\rho = \frac{1}{2}(\mathbb{1}+\vec r\cdot\vec\sigma)$ and collects the three Bloch lengths in $\vec r=(r_A,r_B,r_C)$. It gives (arXiv v2, p. 5, Eq. (10))

> “$\tau(\psi) = 4 \left| \text{Hdet}(t_{ijk}) \right| = 4 \lambda_0^2 \lambda_4^2$.”

The GHZ class is characterized by $\lambda_0\lambda_4\ne0$. Its type 4c states have $\lambda_1=0$, while type 5 requires all $\lambda_j\ne0$ and all $J_k\ne0$. The geometric ansatz is printed as (arXiv v2, p. 7, Eq. (15))

> “$\tau \left( \vec{r} \right) = 1- \frac{\left| \vec{r}\right|^2}{3} - d\left( \vec{r}, V_{\text{line}} \right) \cdot \mathcal{F}\left( \vec{r} \right)$ where $\ket{\psi} \in \text{GHZ}$ excluding type 5 and $\mathcal{F}(\vec{r}) \ge 0$.”

The classification refers to the Acín invariants from A. Acín et al.,
*Generalized Schmidt Decomposition and Classification of Three-Quantum-Bit States*,
Phys. Rev. Lett. 85, 1560–1563 (2000), arXiv:quant-ph/0003050, Eq. (23).
With $μ_j = λ_j^2$ and $Δ = |λ_1 λ_4 e^{iφ} - λ_2 λ_3|^2$, they are
$J_1 = Δ$, $J_2 = μ_0 μ_2$, $J_3 = μ_0 μ_3$, $J_4 = μ_0 μ_4$ and
$J_5 = μ_0(Δ + μ_2 μ_3 - μ_1 μ_4)$.
The full type-5 predicate requires all five amplitudes and all five invariants to be nonzero.

The source defines the distance in Appendix B, before the displayed distance formula:

> “the distance from that point to the straight line spanned by the main diagonal is the length of the vector connecting it to a point on the line such that this vector is perpendicular to the line.”

The formal diagonal is `V_line : Set (EuclideanSpace ℝ (Fin 3)) := Set.range (fun t : ℝ => WithLp.toLp 2 ![t,t,t])`.
The embedding is `euclideanVector r := WithLp.toLp 2 ![r.1,r.2.1,r.2.2]`, and
`distanceToDiagonal r := Metric.infDist (euclideanVector r) V_line` is the infimum
of the Euclidean distances to that line.

The literal density matrix has entries $t_{ijk} \overline{t_{i'j'k'}}$.
Its finite-sum partial traces give $ρ_A$, $ρ_B$ and $ρ_C$.
The Bloch vectors use $(2\operatorname{Re}ρ_{01}, -2\operatorname{Im}ρ_{01},
\operatorname{Re}ρ_{00} - \operatorname{Re}ρ_{11})$.
The three-tangle is $4|\operatorname{Hdet}(t)|$, using Cayley's full quartic;
its canonical specialization $4λ_0^2λ_4^2$ follows by substitution.

The formalized counterexample is the type 4c state
$\frac12(|000\rangle+|101\rangle+|110\rangle+|111\rangle)$. Its reduced states have Bloch lengths $(1/2,1/2,1/2)$, so it lies on the diagonal and the distance term vanishes; its tangle is $1/4$, whereas the ansatz gives $3/4$.

## Verified locator

https://arxiv.org/abs/quant-ph/0003050, Eq. (23), supplies the cited J invariants.

https://arxiv.org/abs/2505.23638v2, pp. 3, 5 and 7, Eqs. (3)–(4), (10) and (15).
