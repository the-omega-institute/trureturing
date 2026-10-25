---
bibkey: nepomechieraveh2024quditdicke
authors: Rafael I. Nepomechie; David Raveh
year: 2024
title: "Qudit Dicke state preparation"
doi: 10.26421/QIC24.1-2-2
url: https://arxiv.org/abs/2301.04989v4
claim: "The paper constructs a deterministic circuit U_n = W_2 ⋯ W_n that prepares every qudit Dicke state from the identity-permutation input, decomposes the qutrit W operators into controlled X and R^y gates I_{m,l} and II_{m,l1,l2}, and conjectures, from experiments, that for fixed occupations the qutrit circuit can be pruned to the gates in the index ranges of its equations W3genericsimple, W3specialsimple and kkdefs while still preparing the Dicke state."
strata_touched:
  - D5/S3/Quantum/PureState/QutritDickePruningRefutation
license: citation-only
triage: anchor
---

# Qudit Dicke state preparation

R. I. Nepomechie and D. Raveh, arXiv:2301.04989v4 [quant-ph]; Quantum Information and Computation 24 (2024), 37–56. Quotations are from the v4 TeX source.

The circuit:

> $U_n =  \overset{\curvearrowright}{\prod_{m=2}^{n}} \left(W_m \otimes  \id^{\otimes(n-m)} \right)\,,$

(the display is written inline here), and

> where the product goes from left to right with increasing $m$.

The conjecture, for the pruned qutrit operators $\widetilde{\widetilde{\mathcal{W}}}_m$ and $\widetilde{\mathcal{W}}_m$ of a fixed occupation vector:

> we conjecture that, similarly to the $d=2$ case \eqref{W2explicit2},

followed by the index ranges (`W3genericsimple`), (`W3specialsimple`) and (`kkdefs`), and:

> We have not yet succeeded to prove the result \eqref{W3genericsimple}-\eqref{kkdefs}, which we found through experimentation.

## Verified locator

Source: https://arxiv.org/abs/2301.04989v4
- URL: https://arxiv.org/abs/2301.04989v4 (source `qdit_v3.tex`, md5 `fcb86a69ac9cdb2a7353251021ea3983`):
  - the Dicke state and the identity-permutation input, l. 177–197;
  - the circuit product, l. 283–288;
  - the elementary and controlled gates, l. 485–527;
  - $V^{(i_0,i_1)}_{m,l}$, $\mathrm{I}_{m,l}$ and their circuits, l. 598–696;
  - $\mathrm{II}_{m,l_1,l_2}$, its angles and circuits, l. 736–881;
  - the unpruned products, l. 900–920;
  - the pruning conjecture, l. 987–1031.
- DOI: 10.26421/QIC24.1-2-2 (https://doi.org/10.26421/QIC24.1-2-2; Crossref lists Quantum Information & Computation, volume 24, issue 1&2, pages 37–56, 2024).
