---
bibkey: zhangnechita2022fisherchannelincompatibility
authors: Qing-Hua Zhang; Ion Nechita
year: 2022
title: "A Fisher information-based incompatibility criterion for quantum channels"
doi: 10.3390/e24060805
url: https://arxiv.org/abs/2204.09963v1
claim: "The paper defines compatibility of quantum channels through a joint channel with the given marginals, proves that compatible channels send every choice of orthonormal bases to compatible projective-test POVMs, conjectures the converse for two channels on the same space, and derives a Fisher information-based incompatibility criterion applied to partially depolarizing channels."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation
license: citation-only
triage: anchor
---

# A Fisher information-based incompatibility criterion for quantum channels

Q.-H. Zhang and I. Nechita, arXiv:2204.09963v1 (only version); Entropy 24(6) (2022), 805. Quotations are from the v1 TeX source.

Channel compatibility (Definition `def:channel-compatibility`):

> Consider two quantum channels $\Phi_1:\mathcal{L}(H_d)\rightarrow \mathcal{L}(H_{d_1})$ and $\Phi_2:\mathcal{L}(H_{d})\rightarrow \mathcal{L}(H_{d_2})$ having the same input space. The pair $(\Phi_1, \Phi_2)$ is said to be *compatible*, if there exists a *joint channel* $\Lambda:\mathcal{L}(H_d)\rightarrow \mathcal{L}(H_{d_1}\otimes H_{d_2})$ such that $\Phi_{1,2}$ are the *marginals* of $\Lambda$:
> $$\forall X \in \mathcal L(H_d), \quad \Phi_1(X) = \operatorname{Tr}_2 \Lambda(X) \quad \text{ and } \quad \Phi_2(X) = \operatorname{Tr}_1 \Lambda(X).$$

POVM compatibility:

> Two POVMs ${\mathbf{A}}=\{A_i\}_{i \in [k]}$ and ${\mathbf{B}}=\{B_j\}_{k \in [l]}$ are said to be *compatible* (or *jointly measurable*) if there exists a third POVM $\mathbf C = \{C_{ij}\}_{(i,j) \in [k] \times [l]}$, called *joint measurement*, such that $A_i = \sum_{j=1}^l C_{ij}$ for all $i \in [k]$ and $B_j = \sum_{i=1}^k C_{ij}$ for all $j \in [l]$.

The partially depolarizing channel:

> $\Phi_t=t\cdot \mathrm{id}+(1-t)\Delta,\qquad 0\leq t\leq 1,$ with $\mathrm{id}(A)=A$ and $\Delta(A)=\operatorname{Tr} A)I_d/d$ for any operator $A$

and

The unmatched parenthesis in $\operatorname{Tr} A)$ is the source's.

> It well known the channel $\Phi_t$ is self-compatible if $0\leq t\leq \frac{d+2}{2(d+1)}$.

Lemma `lem:channel-POVM-compatible` proves that compatible channels $\Phi_1,\ldots,\Phi_N$ give compatible POVMs $\big[\Phi_s^*(|e^{(s)}_i\rangle\langle e^{(s)}_i|)\big]_{i=1}^d$ for all orthonormal bases. The conjecture (Conjecture 4.6, PDF p. 7):

> We leave open the reciprocal question, which we formulate as a conjecture (below for two channels, although the general version, for a $N$-tuple, can be easily stated).

> Consider two quantum channels $\Phi, \Psi: \mathcal L(H_d) \to \mathcal L(H_d)$ such that, for all orthonormal bases $\mathbf e = (e_1, \ldots, e_d)$, $\mathbf f = (f_1, \ldots, f_d)$ of $\mathbb C^d$, the POVMs
> $$\Big[ \Phi^*(|e_i\rangle\langle e_i|) \Big]_{i=1}^d \quad \text{ and } \quad \Big[ \Psi^*(|f_j\rangle\langle f_j|) \Big]_{j=1}^d$$
> are compatible. Then, $\Phi$ and $\Psi$ are compatible channels.

## Verified locator

Source: https://arxiv.org/abs/2204.09963v1
- URL: https://arxiv.org/abs/2204.09963v1 (the e-print is a tar archive; member `article.tex`, md5 `614f0961ea15b65fb0b83ac83bd3fffb`, 548 lines):
  - Definition `def:channel-compatibility`, l. 138–146;
  - the partially depolarizing channel and its self-compatibility range, l. 148–152;
  - POVM compatibility, l. 192–199;
  - Lemma `lem:channel-POVM-compatible` and its proof, l. 239–259;
  - the conjecture, l. 261–266.
- DOI: 10.3390/e24060805 (https://doi.org/10.3390/e24060805; Crossref lists Entropy, volume 24, issue 6, article 805, published 8 June 2022).
