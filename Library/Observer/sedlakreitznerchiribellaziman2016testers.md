---
bibkey: sedlakreitznerchiribellaziman2016testers
authors: Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman
year: 2016
title: "Incompatible measurements on quantum causal networks"
doi: 10.1103/PhysRevA.93.052323
url: https://arxiv.org/abs/1511.00976v2
claim: "Testers (process POVMs) are compatible when they are marginals of a joint tester; the robustness of incompatibility R_t is the least noise weight, with separate noise testers, that makes two testers compatible. For testers with a common normalization state R_t is at most the robustness R_m of their canonical POVMs, with equality for a pure normalization state; whether equality holds for all ancilla-free testers is stated as open."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality
license: citation-only
triage: anchor
---

# Sedlák, Reitzner, Chiribella and Ziman, Incompatible measurements on quantum causal networks

M. Sedlák, D. Reitzner, G. Chiribella and M. Ziman, Phys. Rev. A 93, 052323 (2016); arXiv:1511.00976v2. Quotations are from the v2 TeX source, with the source's macros `\Rt`, `\Rm` and `\st` kept as written.

A tester is a family $\{T_j\}$ of operators on $\mathcal H_1\otimes\mathcal H_0$ with $T_j\ge0$ and $\sum_jT_j=I_1\otimes\rho$ for a density operator $\rho$, the normalization state. Its canonical POVM is $P_j=(I\otimes\rho^{-1/2})T_j(I\otimes\rho^{-1/2})$ on $\mathcal H_1\otimes\operatorname{supp}\rho$. A tester is ancilla-free exactly when $T_j=P_j\otimes\rho$ for a POVM $\{P_j\}$ (Proposition 3). Two testers are $\lambda$-compatible if mixing each with its own noise tester at weight $\lambda$ makes them marginals of a joint tester, and $R_{\rm t}$ is the minimum such $\lambda$; $R_{\rm m}$ is the same notion for POVMs. Proposition 15 gives $R_{\rm t}(\mathsf A,\mathsf B)\le R_{\rm m}(\mathsf P,\mathsf Q)$ for a common normalization state, and Proposition 16 gives equality for a pure one. Section VI.C continues:

> It is an open question whether the equality $\Rt({\st A}, {\st B}) = \Rm( \st P, \st Q )$ holds for all ancilla-free testers.

## Verified locator

Source: https://arxiv.org/abs/1511.00976v2
- DOI: https://doi.org/10.1103/PhysRevA.93.052323 (Physical Review A 93(5), article 052323; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/1511.00976v2. The e-print member `ti_pra_07.tex` has 2205 lines and md5 `613546965b8eca8311e3389eca6d6c24`. Locations:
  - testers and normalization, l. 247–259; canonical POVM, l. 281–303;
  - ancilla-free testers, l. 329–338; compatible testers, l. 451–459;
  - $\lambda$-compatibility and $R_{\rm t}$, l. 567–578; $R_{\rm m}$, l. 760–771;
  - Propositions 15 and 16 and the open question, l. 772–807.
