---
bibkey: ghoshkonarfrancicapalsende2025stabilizer
authors: Debkanta Ghosh; Tanoy Kanti Konar; Gianluca Francica; Amit Kumar Pal; Aditi Sen De
year: 2025
title: "Quantum advantage unlocked: Charging quantum batteries with K-regular graph stabilizers"
doi: null
url: https://arxiv.org/abs/2512.22908v2
claim: "The paper studies quantum batteries whose battery and charging Hamiltonians are sums of the stabilizer generators of K-regular circulant graphs, with the battery prepared in its ground state and charged by unitary evolution; a remark reports that for N ≤ 10 the stored work appears to depend only on the degree difference |K − K′| when N is not a multiple of four."
strata_touched:
  - D5/S3/Quantum/Dynamics/StabilizerBatteryDegreeDifferenceRefutation
license: citation-only
triage: anchor
---

# Quantum advantage unlocked: Charging quantum batteries with K-regular graph stabilizers

D. Ghosh, T. K. Konar, G. Francica, A. K. Pal and A. Sen(De), arXiv:2512.22908v2; v1 was titled "Quantum batteries with K-regular graph generators: A no-go for quantum advantage". Quotations are from the v2 TeX source.

The Hamiltonians:

> We confine ourselves to $H_B$ and $H_C$ having the form $H_{(N,K)}= \sum_{i=1}^NH_{(i,K)},$ with $H_{(i,K)}=\left[\bigotimes_{j=1}^{K/2}Z_{i-j}\right]X_i\left[\bigotimes_{j=1}^{K/2}Z_{i+j}\right],$ where $K$ is even, and has a maximum value $K_{\max}=N-2$ ($N-1$) for even (odd) $N$ with $N>2$.

with periodic boundary conditions, $A_{N+i}\equiv A_i$. The battery Hamiltonian "typically fixes the initial battery-state as its ground state $\ket{\psi_B}$, i.e., $\rho(0)=\ket{\psi_B}\bra{\psi_B}$".

The evolution and the work:

> $\rho(t)=U\rho(0)U^\dagger, \text{with } U=\exp\left[-\text{i}H_C t\right],$ with $H_C=H_{(N,K)}$ as the charging Hamiltonian. The performance of the $K^\prime$-regular battery can be quantified through the \emph{work output}, given by $W_{(N,K^\prime,K)} (t) = \text{Tr}\left[\{\rho(t) - \rho(0)\} H_B\right],$ with $H_B=H_{(N,K^\prime)}$

The remark:

> While our initial investigation with $N\leq 10$ indicates that $W_{(N,K^\prime,K)}$ remains unchanged as long $\Delta = |K-K^{\prime}|$ is constant for $N\neq 4N^\prime$ with $N^\prime=1,2,\cdots$, no such trend is observed in the case of $N\neq 4N^\prime$. However, concrete conclusion requires extensive numerical analysis with large $N$, which is challenging.

The second "$N\neq 4N^\prime$" reads as $N=4N^\prime$.

## Verified locator

Source: https://arxiv.org/abs/2512.22908v2
- URL: https://arxiv.org/abs/2512.22908v2 (source `main_v2.tex`, md5 `483d1a9b1816a8a1a5af8236b8326c6d`):
  - the battery and charging Hamiltonians and the ground state, l. 111–121;
  - the evolution and the work output, l. 145–153;
  - the remark, l. 433.
