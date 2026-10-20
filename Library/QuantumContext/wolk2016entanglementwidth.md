---
bibkey: wolk2016entanglementwidth
authors: Sabine Wölk; Otfried Gühne
year: 2016
title: "Characterizing the width of entanglement"
doi: 10.1088/1367-2630/aa5015
url: https://arxiv.org/abs/1507.07226v2
claim: "The paper introduces the width of entanglement in spin chains, derives criteria from the collective spin and from a magnetic-gradient operator, and conjectures (Appendix D) that every state with entanglement only within the two halves of the chain satisfies a linear upper bound on the gradient second moment in terms of the squared total spin, attained by mixtures of adjacent singlets and the classical state."
strata_touched:
  - D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation
license: citation-only
triage: anchor
---

# Characterizing the width of entanglement

Sabine Wölk and Otfried Gühne, arXiv:1507.07226v2 (quant-ph), 2016-09-06; published in New J. Phys. 18 (2016) 123024. Quotations are from the v2 TeX source.

The gradient operator (Appendix D):

> \BE
> B^{(\ell)}_{k}=(2k-N-1) \sigma^{(\ell)}_{k},
> \EE
> with $\ell=x,y,z$.
> Similar to the angular momentum we define $B^{(\ell)}=\sum_k B^{(\ell)}_{k}$ and $B^2= (B^x)^2+(B^y)^2+(B^z)^2$.  Whereas small values of  $\langle J^2 \rangle$ are indicators for entanglement, large values of $\langle B^2 \rangle$ are indicators for long range correlations, both classical and quantum. As a consequence, all four-qubit states which are separable under the partition $1,2 | 3,4$ obey the inequality

The reference values (Appendix D):

> The only states with $\langle J^2 \rangle=0$ and only next-neighbor entanglement are given by
> \mbox{$\ket{\Psi^-}=\bigotimes\ket{\psi^-}_{2j-1,2j}$}
> which leads to $\langle B^2\rangle_{-}= 6N$. The state
> \mbox{$ \ket{\Psi^\textrm{cl}}=\ket{\uparrow,\dots,\uparrow}_{1,\dots, N/2}\ket{\downarrow,\dots, \downarrow}_{N/2+1,\dots,N} $}
> possess the highest possible value of $\langle B^2 \rangle$ for states with only  entanglement  within the subgroups $\lbrace 1,\dots, N/2\rbrace$ and  $\lbrace N/2+1,\dots, N\rbrace$. This state is characterized by the expectation values $\langle J^2\rangle_\textrm{cl}=2N$ and
> \mbox{$\langle B^2 \rangle_\textrm{cl}=(N^4)/4+2(N-1)N(N+1)/3$}. Therefore, all states with expectation values $\langle B^2 \rangle$ exceeding this bound must posses entanglement between these two subgroups. If we allow entanglement only between nearest neighbors, then compared to $\langle B^2 \rangle_\textrm{cl}$ only the correlation between the two middle particles within the chain are allowed to change from two to six. As a consequence, all states with $\langle B^2 \rangle > \langle B^2 \rangle_\textrm{cl}+4$ posses entanglement beyond nearest neighbors.

The conjecture (Appendix D):

> Furthermore, the behavior of $\langle B^2 \rangle$ for $N=4$ leads us to the conjecture, that the largest possible value of $\langle B^2\rangle$ for a given $\langle J^2\rangle$ with only  entanglement within within the subgroups $\lbrace 1,\dots, N/2\rbrace$ and  $\lbrace N/2+1,\dots, N\rbrace$  is reach by the state
> \mbox{$\varrho=p \ket{\Psi^-}\bra{\Psi^-}+ (1-p)\ket{\Psi^\textrm{cl}}\bra{\Psi^\textrm{cl}}$}.
> %
> As a result, we obtain the conjecture that all states with entanglement only within the subgroups $\lbrace 1,\dots, N/2\rbrace$ and  $\lbrace N/2+1,\dots, N\rbrace$  satisfy the inequality
>  \BE
>  \langle B^2 \rangle \leq \langle B^2\rangle_- + \frac{\langle B\rangle_\textrm {cl}-\langle B^2\rangle_-}{2N}\,\langle J^2\rangle.
>  \EE
> For $N=4$ the conjecture coincides with the inequality given in \eq{theo:mag_grad}. Furthermore, first tests with random states confirm this bound.

## Verified locator

- URL: https://arxiv.org/abs/1507.07226v2 (v2, 2016-09-06; source `ent-distance6_9_16.tex`, md5 `017195d6078fd4bf499d803b9b3c5ac1`): the gradient operator (l. 462–466), the reference values (l. 486–491) and the conjecture (l. 493–500).
- DOI: 10.1088/1367-2630/aa5015 (New J. Phys. 18, 123024). The published text was not read.
