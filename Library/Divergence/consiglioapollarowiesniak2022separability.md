---
bibkey: consiglioapollarowiesniak2022separability
authors: Mirko Consiglio; Tony J. G. Apollaro; Marcin Wieśniak
year: 2022
title: "Variational approach to the quantum separability problem"
doi: 10.1103/PhysRevA.106.062413
url: "https://arxiv.org/abs/2209.01430v2"
claim: "The paper introduces a variational algorithm that finds the closest fully separable state of a multiqubit state in the Hilbert–Schmidt distance, applies it to GHZ states and to maximally entangled mixed X-states (X-MEMS), and conjectures an explicit form (A11) for the closest separable state of the n-qubit X-MEMS."
strata_touched:
  - D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation
license: citation-only
triage: anchor
---

# Consiglio, Apollaro and Wieśniak, Variational approach to the quantum separability problem

M. Consiglio, T. J. G. Apollaro and M. Wieśniak, Physical Review A 106(6) (2022) 062413, DOI 10.1103/PhysRevA.106.062413; arXiv:2209.01430v2 (titled "A Variational Approach to the Quantum Separability Problem"). Quotations are from the arXiv v2 TeX source.

The Hilbert–Schmidt distance is $D_{HS}(\rho,\sigma)=\operatorname{Tr}(\rho-\sigma)^2$, the induced entanglement measure is its minimum over the fully separable states, and the closest separable state (CSS) is the minimizer. The $n$-qubit X-MEMS with $N=2^{n-1}$ has diagonal $f(\gamma)$ at $|0\cdots0\rangle$, $g(\gamma)$ at the other $N-1$ words with first bit $0$ and at $|1\cdots1\rangle$, $0$ at the remaining words, and corner entries $\gamma,\gamma^*$; on $0\le|\gamma|\le\frac1{N+1}$, $f=g=\frac1{N+1}$. For it the paper states:

> While we have not explicitly derived the CSS of $n$-qubit X-MEMS in general, we conjecture that it is of the form

followed by the matrix (A11) with diagonal $\frac a2$ at $|0\cdots0\rangle$ and $|1\cdots1\rangle$, $\frac b{N-1}$ at the other first-bit-$0$ words, $\frac{1-a-b}{N-1}$ at the other first-bit-$1$ words and corner entries $d,d^*$, where $a,b\in[0,1]$, $a+b\le1$ and $|d|\le\frac a2$.

## Verified locator

Source: https://arxiv.org/abs/2209.01430v2
- DOI: https://doi.org/10.1103/PhysRevA.106.062413 (journal version; title, authors, journal, volume, issue and article number from Crossref; the journal text was not read).
- URL: https://arxiv.org/abs/2209.01430v2. The e-print member `PRA_v2.tex` has 585 lines and md5 `611cfcad16eb65b213bb7ddff8372815`. Locations:
  - the Hilbert–Schmidt distance, the induced measure and the CSS, l. 70–80;
  - the X-MEMS, Appendix A, l. 341–373;
  - the three-qubit form derived under the PPT constraint, l. 426–455;
  - the conjecture (A11), l. 459–474.
