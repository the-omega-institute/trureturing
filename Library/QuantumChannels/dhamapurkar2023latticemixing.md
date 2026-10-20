---
bibkey: dhamapurkar2023latticemixing
authors: Shyam Dhamapurkar; Xiu-Hao Deng
year: 2023
title: "Quantum walk mixing is faster than classical on periodic lattices"
doi: 10.1016/j.physa.2023.129252
url: https://arxiv.org/abs/2309.16352v1
claim: "For the continuous-time quantum walk on Z_n, the time-dependent part of the transition probability is n(t) = sum over 0 <= j, k <= n - 1 with j != k and j + k != n of exp(-i t sin(pi (j+k)/n) sin(pi (j-k)/n)) w^((q-p)(j-k)), w = exp(2 pi i/n) (Eq. (B8)). The paper conjectures (Conjecture 1, Eq. (14)) a bound on the time integral of products of such terms for odd, pairwise coprime n_1 > ... > n_d, and uses the case d = 2, |int_0^T n_1(t) n_2(t) dt| <= 32 n_1 (n_2 log n_2)^2 + 32 n_2 (n_1 log n_1)^2 (Eq. (15)), in its mixing-time theorem."
strata_touched:
  - D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation
license: citation-only
triage: anchor
---

# Quantum walk mixing is faster than classical on periodic lattices

Shyam Dhamapurkar, Xiu-Hao Deng, Physica A 630, 129252 (2023),
arXiv:2309.16352v1 (quant-ph). Quotations are from the arXiv v1 TeX source,
with equation numbers as in the arXiv v1 PDF.

The time-dependent term of the walk on $\mathbb{Z}_n$ (Eq. (B8)):

> $n(t) = \sum_{j,k = 0,j \neq k,j+k \neq n}^{n-1} e^{-it(\sin{(\pi (j+k)/n)}\sin{(\pi (j-k)/n)})} w^{(q-p)(j-k)}$

with $w = e^{2\pi i/n}$ and $p$, $q$ the start and end vertices. On
$\mathbb{Z}_{n_1}\times\mathbb{Z}_{n_2}$ the walk runs for time $t/2$ in each
factor, and the paper writes $n_1(t)$, $n_2(t)$ for these terms with
displacements $l_1$, $l_2$.

Conjecture 1 (Eq. (14)):

> For $n_1 > n_2 > \dots > n_d$, where $n_1, n_2, \dots, n_d$ are odd and relatively prime, we have $\left|\int_0^T \prod_{i=1}^d n_i(t)dt \right|\leq 16 d \sum_{j= 1}^{d} \left(\prod_{i \neq j}^d n_i(t)\right)  (n_j\log(n_j))^2.$

The case used in the mixing-time theorem (Eq. (15)):

> In the proof of Theorem \ref{thm3} we use specific case $d=2$ of the conjecture, i.e., for $\mathbb{Z}_{n_1}\times \mathbb{Z}_{n_2}$: $\left| \int_{0}^{T} n_1(t) n_2(t) dt \right|\leq 32 n_1(n_2 \log(n_2))^2+ 32 n_2(n_1 \log(n_1))^2.$

The numerical support (Appendix F):

> We considered pairs $(n_1, n_2)$ such that $n_1 > n_2$ are odd and relatively prime, and in the range $[10, 200]$.

## Verified locator

- DOI: https://doi.org/10.1016/j.physa.2023.129252 (the published
  version was not read).
- URL: https://arxiv.org/abs/2309.16352v1 (v1, 2023-09-28, the only
  version; source `main.tex`, md5 `7dd33193855e62a751f54973ef4e158c`):
  Conjecture 1 and Eq. (15) (l. 329–343), Eq. (B8) (l. 565–567) and the
  numerical support (l. 825).
