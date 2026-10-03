---
bibkey: bai2007multipartite
authors: Yan-Kui Bai; Dong Yang; Z. D. Wang
year: 2007
title: "Multipartite quantum correlation and entanglement in four-qubit pure states"
doi: 10.1103/PhysRevA.76.022336
url: https://arxiv.org/abs/quant-ph/0703098v2
claim: "For a four-qubit pure state, tau_k = 2(1 - tr rho_k^2) is the linear entropy of qubit k and C_ij = max(sqrt(lambda_1) - sqrt(lambda_2) - sqrt(lambda_3) - sqrt(lambda_4), 0) is the concurrence of the pair ij, where lambda_1 >= ... >= lambda_4 are the eigenvalues of rho_ij (sigma_y x sigma_y) rho_ij^* (sigma_y x sigma_y). The sum of the residual correlations is M = sum_k tau_k - 2 sum_{p>q} C_pq^2 (Eq. (7)), and the authors conjecture that M is an entanglement monotone, that is, does not increase on average under LOCC."
strata_touched:
  - D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation
license: citation-only
triage: anchor
---

# Multipartite quantum correlation and entanglement in four-qubit pure states

Yan-Kui Bai, Dong Yang, Z. D. Wang, Phys. Rev. A 76, 022336 (2007);
arXiv:quant-ph/0703098v2. Quotations are from the arXiv v2 source, with its
macros kept as printed.

The linear entropy of qubit $k$:

> where the linear entropy $\tau_{k(R_k)}=2(1-\mbox{tr}\rho_k^2)$ \cite{san00} characterizes the total quantum correlation between qubit $k$ and the remaining qubits $R_k$.

The concurrence of a pair of qubits:

> $C_{ij}=\mbox{max}[(\sqrt{\lambda_{1}}-\sqrt{\lambda_{2}}- \sqrt{\lambda_{3}}-\sqrt{\lambda_{4}}), 0]$, where the decreasing positive real numbers $\lambda_{i}$s are the eigenvalues of matrix $\rho_{ij}(\sigma_y\otimes\sigma_y)\rho_{ij}^{\ast}(\sigma_y\otimes\sigma_y)$ \cite{woo01}.

The requirement on a multipartite measure:

> (3) it does not increase on average under the LOCC \emph{i.e.}, the measure is entanglement monotone.

The sum of the residual correlations (Eq. (7)):

> $M=M_{A}+M_{B}+M_{C}+M_{D}=\sum_{k}\tau_{k(R_k)}-2\sum_{p>q}C_{pq}^{2}$,

The conjecture:

> Nevertheless, we conjecture that the correlation $M$ is an entanglement monotone

The paper supports the conjecture with an argument that the decrease of two
components of $M$ under a POVM on qubit $A$ compensates the increase of the
third, and with numerical values of the average change of $M$ for nine
representative states of the SLOCC classification under diagonal two-outcome
POVMs with diagonal entries $\alpha,\beta\in[0.05,0.95]$ (Fig. 2). It also
proves that the single residual correlation $M_A$ does not increase on
average under a POVM on qubit $A$ (Eq. (6)), and shows by examples in the
Appendix that the single residual correlations $M_k$ are not entanglement
monotones.

The encoding takes four-qubit vectors as functions
$(\mathrm{Fin}\,4\to\mathrm{Fin}\,2)\to\mathbb C$, qubits $A,B,C,D$ at the
indices $0,1,2,3$; the one- and two-qubit reduced states are the existing
partial traces `reducedState`, the matrix
$(\sigma_y\otimes\sigma_y)\rho^\ast(\sigma_y\otimes\sigma_y)$ is the existing
`timeReversed`, the eigenvalues are the roots of the characteristic
polynomial, with multiplicity, sorted decreasingly, and a $2\times2$ matrix
$K$ acts on qubit $A$ as the existing `localOp 0 K`.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.76.022336 (Phys. Rev. A 76, 022336
  (2007)).
- URL: https://arxiv.org/abs/quant-ph/0703098v2 (v2, 2007-09-01, the latest
  version; source `Four-qubit-31Jul.tex`, md5
  `aa80185a0631338fccbaf59466008d55`): the linear entropy (l. 139–141), the
  concurrence (l. 199–205), the monotonicity requirement (l. 225–229),
  Eq. (6) (l. 263–266), Eq. (7) (l. 362–366), the conjecture (l. 374–375),
  the compensation argument (l. 376–390), the numerical evidence (l.
  392–422), the per-qubit measure $E_{ms}=M/4$ (l. 453–465) and the
  $N$-qubit sum $M_N$ (l. 518–528).
