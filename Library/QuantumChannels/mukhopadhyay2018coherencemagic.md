---
bibkey: mukhopadhyay2018coherencemagic
authors: Chiranjib Mukhopadhyay; Sk Sazim; Arun Kumar Pati
year: 2018
title: "Coherence makes quantum systems 'magical'"
doi: 10.1088/1751-8121/aac8e8
url: https://arxiv.org/abs/1801.04807v3
claim: "For a qutrit density matrix rho with rho_12 = lambda_1 + i mu_1, rho_13 = lambda_2 + i mu_2, rho_23 = lambda_3 + i mu_3, the paper gives the nine entries of the discrete Wigner function and the sum negativity M_SN = sum |W_u| - 1 (Eq. (13)). From numerical simulation it states, for pure qutrit states, M_SN >= (C/2) sqrt(1 - C/2) with C the l1-norm coherence (Eq. (18)), and for qutrit-qubit states the trade-off 16 E_AB^2 + 9 M_SN_A^2 < 4 (Eq. (19))."
strata_touched:
  - D5/S3/Quantum/Information/QutritMagicCoherenceBound
license: citation-only
triage: anchor
---

# Coherence makes quantum systems 'magical'

Chiranjib Mukhopadhyay, Sk Sazim, Arun Kumar Pati, J. Phys. A: Math. Theor.
51, 414006 (2018), arXiv:1801.04807v3 (quant-ph). Quotations are from the
arXiv v3 TeX source; `cohbound` and `entbound` label the panels (a) and (b) of Fig. 4.

The qutrit Wigner function:

> For the qutrit case, after some algebra, we have the following discrete Wigner distribution corresponding to a qutrit density matrix $\rho$. $W_{(1,1)} = \frac{1}{3}(2\lambda_3 + \rho_{11})$, $W_{(1,2)} = \frac{1}{3}(2\lambda_2 + \rho_{22})$, $W_{(1,3)} = \frac{1}{3}(2\lambda_1 + \rho_{33})$, $W_{(2,1)} = \frac{1}{3}(-\lambda_3 - \sqrt{3}\mu_3 + \rho_{11})$, $W_{(2,2)} = \frac{1}{3}(-\lambda_2 + \sqrt{3}\mu_2 + \rho_{22})$, $W_{(2,3)} = \frac{1}{3}(-\lambda_1 - \sqrt{3}\mu_1 + \rho_{33})$, $W_{(3,1)} = \frac{1}{3}(-\lambda_3 + \sqrt{3}\mu_3 + \rho_{11})$, $W_{(3,2)} = \frac{1}{3}(-\lambda_2 - \sqrt{3}\mu_2 + \rho_{22})$, $W_{(3,3)} = \frac{1}{3}(-\lambda_1 + \sqrt{3}\mu_1 + \rho_{33})$. Where density matrix elements $\rho_{12} = \lambda_1 + i\mu_1, \rho_{13} = \lambda_2 + i\mu_2, \rho_{23} = \lambda_3 + i\mu_3$.

> Now the sum negativity $M_{SN}[\rho]$ is simply given by $M_{SN}[\rho] = \sum_{\textbf{u}}|W_{\textbf{u}}| - 1$.

The coherence lower bound (Eq. (18)):

> However, for qutrit pure states, numerical simulation in Fig. \ref{cohbound} leads us to conjecture the following inequality, which gives a reverse, i.e., lower bound to the magic in terms of quantum coherence.
> Proposition - The following condition on quantum coherence, quantified via the $l_1$-norm, and 'magic', quantified by the sum negativity, holds for qutrit pure states $M_{SN}[|\psi\rangle] \geq \frac{C_{l_{1}}[|\psi\rangle]}{2}\sqrt{1- \frac{C_{l_{1}}[|\psi\rangle]}{2}}$

The entanglement trade-off (Eq. (19)):

> Proposition - The negativity of entanglement $E_{AB}$ and the sum negativity $SN_{A}$ satisfies the following trade off relation $16 E_{AB}^{2} + 9 M_{SN_{A}}^{2} < 4$. Although an analytical proof is lacking, the numerical result furnished in Fig. \ref{entbound} strongly suggests that the proposition above is true and indeed, almost tight for pure $3\times2$ states.

## Verified locator

- DOI: https://doi.org/10.1088/1751-8121/aac8e8 (the published version was
  not read).
- URL: https://arxiv.org/abs/1801.04807v3 (v3, 2018-05-30, the latest
  version; source `coherence_vs_magic.tex`, md5
  `4da28ae07308172cbefcc4b09ae2b7b6`): the Wigner function (l. 272–282),
  the sum negativity (l. 284), Eq. (18) (l. 368–371) and Eq. (19)
  (l. 374–382).
