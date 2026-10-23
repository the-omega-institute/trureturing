---
bibkey: hanliu2023twirling
authors: Deguang Han and Kai Liu
year: 2023
title: "Zero-Error Correctibility and Phase Retrievability for Twirling Channels"
doi: 10.1016/S0034-4877(24)00012-0
url: https://arxiv.org/abs/2311.16349v1
claim: "Section 5 conjectures pr(Phi_pi) = max{beta(Phi_pi), k} when I_k <= d < I_(k+1), for d inequivalent irreducible summands with positive multiplicities; Theorem 3.4 proves beta(Phi_pi) = max_i m_i."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1016/S0034-4877(24)00012-0

Source: https://arxiv.org/abs/2311.16349v1

The arXiv version is dated 27 November 2023. The journal citation is
*Reports on Mathematical Physics* 93(1) (2024), 87–102. Page numbers below
refer to the arXiv PDF.

## Definitions and conjecture

The twirling channel is defined on page 3:

> We define a linear map $\Phi_{\pi, \sigma}: B(K, H)\to B(K, H)$ by
> $\Phi_{\pi, \sigma}(T) = \int_{G}\pi(g)T\sigma(g^{-1}) d\mu(g)$
> and denote $\Phi_{\pi, \sigma}$ by $\Phi_{\pi}$ when $\pi = \sigma$.

For finite groups, normalized Haar integration is the average over the group.
Unitarity identifies the inverse with the matrix star.

Page 5 defines phase retrievability:

> A subspace $M$ of $H$ is called phase retrievable under $\Phi$ if $\Phi$ is pure state injective on $M$, i.e., $\Phi(x\otimes x) = \Phi(y\otimes y)$ implies that $x\otimes x = y\otimes y$ for $x, y\in M$, or equivalently if there exists a POVM $\{F_{j}\}_{j\in\mathbb{J}}$ in $B(K)$ such that $\{P_{M}\Phi^*(F_{j})P_{M}\}_{j\in\mathbb{J}}$ is a phase retrievable operator valued frame for $M$, where $P_M$ is the orthogonal projection onto $M$.

> The phase retrievability index $pr(\Phi_{\pi})$ is defined to be the largest integer $k$ such that there exits a $k$-dimensional subspace $M\subset H$ such that $M$ is phase retrievable under $\Phi$.

The spelling “exits” is retained from the source. Rank-one states are encoded
by `Matrix.vecMulVec x (star x)`, and the largest admissible dimension by the
natural supremum.

Page 4 defines the frame length:

> For an $n$-dimensional Hilbert space $H$, we will use $\mathcal{I}_n$ to denote the smallest integer $N$ such that there is a phase retrievable frame $\{x_{j}\}_{j=1}^{N}$ for $H$.

The encoding uses complex coordinate spaces, `Fin n` for a family of length
$n$, and the natural infimum. A family that retrieves every rank-one state
spans the space: a nonzero vector orthogonal to the family would have the
same measurements as zero.

Lemma 3.1 on page 5 characterizes codes:

> Let $\mathcal{C}$ be a subspace of $H$, and let $P$ be the orthogonal projections onto $\mathcal{C}$. Suppose $\Phi$ is a quantum channel with Kraus operators $\{E_i\}_{i=1}^{r}$. Then the following are equivalent:

Its items (i) and (ii) are:

> $\mathcal{C}$ is a quantum code for $\Phi$.

> there exists a Hermitian matrix $A = [a_{ij}]$ such that $PE_i^*E_jP = a_{ij}P$ holds for all $i, j$.

`IsCode` uses this compression condition. A self-adjoint idempotent with
range $M$ is the orthogonal projection onto $M$. For the twirl, the Kraus
operators are $\pi(g)/\sqrt{|G|}$, whose common positive normalization can be
absorbed in the compression scalars. Those scalars are automatically
Hermitian when the projection is nonzero; for the zero code one may choose
them all zero. The index $\beta$ is the largest code dimension. Theorem 3.4
on page 7 proves $\beta(\Phi_\pi) = \max\{m_1, ... , m_d\}$.

The representation conventions use invariant complex subspaces and an
invertible complex-linear intertwiner. An irreducible representation acts
on a nonzero space. The block representation is the direct sum of
$I_{m_i}\otimes\rho_i$, indexed by `Σ i, Fin (m i) × Fin (n i)`.

The final conjecture of Section 5, page 13, reads:

> **Conjecture.** Let $\pi = m_1\pi_1\oplus ... \oplus m_d\pi_d$ be a unitary representation of $G$ such that $\pi_i$ and $\pi_j$ are inequivalent irreducible representations for all $i\neq j$ and $\mathcal{I}_k \leq d < \mathcal{I}_{k+1}$. Then $pr(\Phi_\pi) = \max \{\beta(\Phi_{\pi}), k\}$.

The public `claim` specializes this assertion to finite groups, includes
positive multiplicities, and quantifies all decomposition data. A
counterexample to this specialization refutes the compact-group conjecture.

## Counterexample and boundary

For $C_3$, each of the three one-dimensional characters appears twice.
Character orthogonality makes the twirl the three-block pinching. The
encoding $(u,v,w)\mapsto((u,v),(u,w),(v,w))/\sqrt2$ retains every entry of a
$3\times3$ operator in its three $2\times2$ compressions. Its range therefore
has phase retrievability dimension three. The code dimension is two,
and $\mathcal I_1\le3<\mathcal I_2$, giving $k=1$. These facts yield the
module's `result : ¬ claim`.

The rectangular encoding matrix uses `Matrix.conjTranspose`; square
matrices retain `star`. Nonzero dimension is included in irreducibility.
Both conventions preserve the mathematical meaning of the source.

The multiplicity-one character case proved immediately before the conjecture
is compatible with this counterexample. The source's code-dimension theorem
and its phase-retrievability lower bounds also remain compatible. The module
does not determine the exact index for general multiplicities or groups.
