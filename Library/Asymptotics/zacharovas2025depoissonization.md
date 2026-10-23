---
bibkey: zacharovas2025depoissonization
authors: Vytas Zacharovas
year: 2025
title: An Elementary Approach to Depoissonization
doi: null
url: https://arxiv.org/abs/2511.14324v2
claim: Theorem 2.8 bounds arbitrary-center Poisson–Charlier truncation error using an absolute Poisson average of the next derivative's coefficients; it imposes no zero-location or Laguerre–Polya hypothesis.
strata_touched:
  - D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering
license: citation-only
triage: anchor
---

# An arbitrary-center coefficient supplier

For a real sequence $(u_\ell)_{\ell\ge0}$ whose exponential generating
series is entire, write

$$
g(z)=e^{-z}\sum_{\ell\ge0}u_\ell z^\ell/\ell!,
\qquad
\mathscr E(g;\rho)=e^{-\rho}
\sum_{\ell\ge0}|u_\ell|\rho^\ell/\ell!.
$$

The source uses the Charlier normalization

$$
\mathsf C_j(\rho,\ell)=
\sum_{k=0}^j(-1)^{j-k}\binom jk
              \frac{\ell^{\underline k}}{\rho^k}.
$$

[Theorem 2.8](https://arxiv.org/html/2511.14324v2#S2.Thmthm8)
states, for every $\rho>0$, integer $\ell\ge2$ and $N\ge0$,

$$
\left|u_\ell-\sum_{j=0}^N
\frac{g^{(j)}(\rho)}{j!}\rho^j\mathsf C_j(\rho,\ell)\right|
\le 12\,\frac{\ell!e^\rho}{\rho^\ell}
             \ell^{N/2}\mathscr E(g^{(N+1)};\rho).
$$

Here $\mathscr E(g^{(j)};\rho)$ uses the coefficients of
$e^zg^{(j)}(z)$, equivalently the $j$th forward differences of $u_\ell$.
It is not generally $|g^{(j)}(\rho)|$. Theorem 1.2's center $\rho=\ell$
and constant 33 are a separate specialization; the arbitrary center above
is retained for the source-zero application.

[Corollary A.6](https://arxiv.org/html/2511.14324v2#A1.Thmthm6)
gives the displayed finite-sum normalization. In DLMF's convention,
$\mathsf C_j(\rho,\ell)=(-1)^jC_j(\ell;\rho)$.
[DLMF 18.21.9](https://dlmf.nist.gov/18.21.E9) supplies

$$
\lim_{a\to\infty}(2a)^{j/2}
C_j(a+\sqrt{2a}\,y;a)=(-1)^jH_j(y).
$$

These are cited results, not new convergence or depoissonization
theorems. The theorem applies to real coefficient sequences without
assuming real-rootedness of $g$. The [original-source application](../Analytic/romik2021orthogonal.md)
must separately map its coefficients, control this remainder and capture
the actual polynomial nodes. A generic supplier is not an all-height
Jensen margin or an RH/Robin proof.

The inspected source is arXiv:2511.14324v2, revised 3 September 2026.
The initial preprint is from 18 November 2025.
