---
bibkey: basslerheinrichkliesch2024gzz
authors: Pascal Baßler; Markus Heinrich; Martin Kliesch
year: 2024
title: "Time-optimal multi-qubit gates: Complexity, efficient heuristic and gate-time bounds"
doi: 10.22331/q-2024-03-13-1279
url: https://arxiv.org/abs/2307.11160v2
claim: "The paper casts the time-optimal synthesis of global ZZ gates as a linear program over the cut-polytope vertices m m^T, proves gate-time bounds and a tightness theorem for M = -C m m^T, and conjectures that the optimal gate time is at most the largest coupling times n (odd n) or n-1 (even n)."
strata_touched:
  - D5/S3/Quantum/Optimization/GlobalZZGateTimeBound
license: citation-only
triage: anchor
---

# Time-optimal multi-qubit gates: complexity, efficient heuristic and gate-time bounds

P. Baßler, M. Heinrich and M. Kliesch, arXiv:2307.11160v2 [quant-ph]; Quantum 8, 1279 (2024). Quotations are from the v2 TeX source (`\HTL` is `\mathrm{Sym}_0`, `\linfnorm{M}` is $\|M\|_{\ell_\infty}$).

The linear program:

> Our objective is to minimize the total gate time and the amount of $\vec m$'s needed to express the matrix $M \in \HTL(\RR^n)$. To this end we formulate the following \acf{LP}: minimize $\vec 1^T \vec \lambda$ subject to $V \vec \lambda =\vec v(M)$, $\vec \lambda \in \R^{2^{n-1}}_{\geq 0}$

(the optimization display is written inline here).

The conjecture (Conjecture `conj:gate-time`):

> The optimal gate time of $\Gate{GZZ}(A)$ with $A \in \HTL (\RR^n)$ is tightly upper bounded by $\vec 1^T \vec \lambda^* \leq \linfnorm{ M } \cdot n$ for odd $n$, $n-1$ for even $n$.

(the `cases` display is written inline here).

The status:

> Unfortunately, we were not able to prove this result and state the challenges in \cref{app:proof_problems}.

## Verified locator

Source: https://arxiv.org/abs/2307.11160v2
- URL: https://arxiv.org/abs/2307.11160v2 (source `J_shaping.tex`, md5 `3c751c31a7a40505b6013390b841878a`):
  - $\mathrm{Sym}_0$, l. 240;
  - the linear program, l. 270–290;
  - the norms, l. 448;
  - the conjecture, l. 919–927;
  - the tightness theorem, l. 1121–1130;
  - the status sentence, l. 349.
- DOI: 10.22331/q-2024-03-13-1279 (https://doi.org/10.22331/q-2024-03-13-1279; Crossref lists Quantum, volume 8, article 1279, published 13 March 2024).
