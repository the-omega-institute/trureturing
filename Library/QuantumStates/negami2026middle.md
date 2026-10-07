---
bibkey: negami2026middle
authors: H. Negami
year: 2026
title: "Quantum gates from the middle convolution of twisted Burau representations"
doi: 10.48550/arXiv.2610.00293
url: https://arxiv.org/abs/2610.00293v1
claim: "Problem 6.8, last sentence: prove the Jordan obstruction for the Jones-Temperley-Lieb endpoint-sector seeds of Remark 6.7(b), whose ambient Long-Moody braid matrices were found numerically to have non-trivial Jordan blocks."
strata_touched:
  - D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction
license: citation-only
triage: anchor
---

# Quantum gates from the middle convolution of twisted Burau representations

H. Negami, arXiv:2610.00293v1 (2026-09-25), quant-ph, cross-listed math-ph; only v1
exists. Theorem-like environments share one counter per section: Remark 6.7 and
Problem 6.8 are in §6.1.1 (*Open questions: irreducibility and image closure*).

The open item, verbatim (Problem 6.8, last sentence):

> Also prove the Jordan obstruction for the Jones--Temperley--Lieb endpoint-sector seeds in Remark~\ref{rem:numerics}(b).

The summary table row for these seeds ends:

> Finite-precision tests suggest Jordan blocks and show large norms of sampled words. An exact obstruction remains open.

Remark 6.7(b), verbatim excerpts:

> let $\mathcal P_{m,\ell}$ be the Hilbert space with orthonormal basis the length-$m$ paths on the $A_{\ell-1}$ graph starting at its left endpoint; the usual path-model Temperley--Lieb operators $E_i$ satisfy

> E_i^2=\delta_\ell E_i,\qquad \delta_\ell=2\cos(\pi/\ell).

> \rho(\sigma_i)=\alpha_\ell I+\beta_\ell E_i,\qquad \alpha_\ell=i e^{-\pi i/(2\ell)},\qquad \beta_\ell=\alpha_\ell^{-1},

> with no additional scalar twist; thus $q=\alpha_\ell^{-4}$.

> The terminal vertex of a path is preserved, so $\mathcal P_{m,\ell}$ is the orthogonal direct sum of its \emph{endpoint sectors}; these are the sectors used below.

> We restrict each endpoint sector of the $B_{n+1}$ representation to $F_n\rtimes B_n\cong B_{1,n}$ as in Section~\ref{subsec:klm}, and use that restriction as the KLM seed.

> The ancillary script checks every endpoint sector of dimension at least two for $n=3$, $\ell\in\{4,5,6,7,8,10,12,16\}$, and for $n=4$, $\ell\in\{5,7\}$. It tests the ambient LM braid matrices \eqref{eq:braid-matrices} only in sectors for which its numerical kernel test gives $K=0$; otherwise it reports the kernel dimension and skips the sector, without forming a quotient. Finite-precision rank tests suggest the presence of non-trivial Jordan blocks, and sampled random words of length $300$ have large operator norms, of orders $10^{3}$--$10^{15}$. These finite-precision observations motivate an exact Jordan obstruction; by themselves they establish neither non-semisimplicity nor unboundedness.

The identification $F_n\rtimes B_n\cong B_{1,n}$ (Definition 1.7), the Long–Moody
operators (Definition 1.4, Eq. `eq:braid-matrices`) and $K$ (Definition 1.5), verbatim:

> $x_1=\sigma_0^2$ and $x_{j+1}=\sigma_jx_j\sigma_j^{-1}$.

> S_i&:=\rho^{\mathrm{LM}}_\lambda(\sigma_i) =s_i^{\oplus n} \begin{pmatrix} I_{N(i-1)}&0&0\\ 0&R_i&0\\ 0&0&I_{N(n-i-1)} \end{pmatrix},\\[2pt] R_i&:=\begin{pmatrix}0&g_i\\I_N&I_N-g_{i+1}\end{pmatrix}.

> K&:=\{(v_1,\ldots,v_n)\in V^{\oplus n}:\ v_j\in\Ker(g_j-I_N)\text{ for every }j\},

Here $g_j=\rho(x_j)$ and $s_i=\rho(\sigma_i)$; the generators of $B_{n+1}$ are
$\sigma_0,\dots,\sigma_{n-1}$ and $m=n+1$.

## Verified locator

DOI: `10.48550/arXiv.2610.00293`. Canonical source URL: `https://arxiv.org/abs/2610.00293v1`.
Problem 6.8 and Remark 6.7 are in §6.1.1; the Long–Moody operators are Eq.
`eq:braid-matrices` (Definition 1.4), $K$ is in Definition 1.5 and the identification
$x_1=\sigma_0^2$ is in Definition 1.7.
