---
bibkey: zhouwuchau2016errordisturbance
authors: S.S. Zhou; Shengjun Wu; H.F. Chau
year: 2016
title: "State-independent error-disturbance trade-off for measurement operators"
doi: 10.1016/j.physleta.2016.03.046
url: https://arxiv.org/abs/1509.03812v1
claim: "For rank-one projective measurements A, A' and B on C^d, the state-independent error of replacing A by A', the disturbance that A' causes to B, and their overall error Delta(A,A',B) are maxima over states of infinity-norm distances between outcome distributions. The paper proves trade-offs for qubits and for mutually unbiased A and B, and conjectures, with the error between A and B relaxed to ignore outcome labels, that eps(A,A')+eta(A',B) and Delta(A,A',B) are both at least min{eps(A,B), eta(A,B)} in every dimension."
strata_touched:
  - D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation
license: citation-only
triage: anchor
---

# Zhou, Wu and Chau, State-independent error-disturbance trade-off for measurement operators

S. S. Zhou, S. Wu and H. F. Chau, arXiv:1509.03812v1 [quant-ph]; Physics Letters A 380(22–23), 1918–1924 (2016). Quotations are from the v1 TeX source, with the source's macros `\ket`, `\bra` and `\braket` kept as written.

Section II measures the deviation between outcome distributions by $D(x,y)=\max_i|x_i-y_i|$ and defines, for a state $\rho$ and the state $\rho'=\sum_i\langle a'_i\rvert\rho\lvert a'_i\rangle\,\lvert a'_i\rangle\langle a'_i\rvert$ after the measurement $\mathcal A'$,
$$\varepsilon_\rho(\mathcal A,\mathcal A')=D(P_{\mathcal A}(\rho),P_{\mathcal A'}(\rho)),\qquad\eta_\rho(\mathcal A',\mathcal B)=D(P_{\mathcal B}(\rho),P_{\mathcal B}(\rho')),$$
the state-independent error and disturbance $\varepsilon(\mathcal A,\mathcal A')=\max_\rho\varepsilon_\rho$ and $\eta(\mathcal A',\mathcal B)=\max_\rho\eta_\rho$, and

> the \textbf{state-independent overall error} $\Delta(\mathcal{A}, \mathcal{A}', \mathcal{B}) = \max_\rho \left( \varepsilon_{\rho}(  \mathcal{A}, \mathcal{A}') + \eta_{\rho}(  \mathcal{A}', \mathcal{B})\right).$

Before the conjecture the error between $\mathcal A$ and $\mathcal B$ is relaxed:

> $\varepsilon(\mathcal{A},\mathcal{B}) = \min_{\tilde{\mathcal B}} \varepsilon(\mathcal{A},\tilde{\mathcal{B}})$, where the minimum is over all possible projective measurements with rank one projectors $\tilde{\mathcal B}$ corresponding to the measurement operation $\mathcal{B}$.

Conjecture 3 (label `thm:conj`):

> For all $d \geq 2$, the following trade-off between error and disturbance holds: $\varepsilon(\mathcal{A},\mathcal{A}') + \eta(\mathcal{A}',\mathcal{B}) \geq f(\mathcal{A},\mathcal{B})$ and $\Delta(\mathcal{A},\mathcal{A}',\mathcal{B}) \geq f(\mathcal{A},\mathcal{B})$, where $f(\mathcal{A},\mathcal{B}) = \min \{ \varepsilon(\mathcal{A},\mathcal{B}),\eta(\mathcal{A},\mathcal{B}) \}$. Moreover, the equalities are both attained either when for all $i$, $\ket{a'_i} = \ket{a_i}$, or when for all $i$, $\ket{a'_i} = \ket{b_i}$.

## Verified locator

Source: https://arxiv.org/abs/1509.03812v1
- DOI: https://doi.org/10.1016/j.physleta.2016.03.046 (Physics Letters A 380(22–23), 1918–1924, May 2016; title, authors, journal, volume, issue and pages from Crossref).
- URL: https://arxiv.org/abs/1509.03812v1. The e-print is a gzipped tar archive; its member `new_912arxiv.tex` has 971 lines and md5 `224f302edfcd0f7e887b2c9695c86591`. Locations:
  - the post-measurement state, l. 175–176;
  - the state-dependent error and disturbance, l. 185 and l. 190; the infinity-norm distance, l. 196;
  - the state-independent error, disturbance and overall error, l. 203, l. 208 and l. 220;
  - Theorem 1 (qubits), l. 457; Theorem 2 (mutually unbiased bases), l. 552;
  - the relaxed error, l. 614–620; Conjecture 3, l. 623–639.
- The journal text was not read; that it states the same conjecture is not verified here.
