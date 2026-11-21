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
  - D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality
  - D5/S3/Quantum/QuantumChannels/SedlakWeightedTesterCover
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

## Maximal incompatibility (§V.C)

Proposition 12 equates effectwise orthogonality ($A_j B_k=0$ for all outcomes) with orthogonality of the normalization states ($\rho\sigma=0$). Orthogonal testers attain $R_{\rm t}=1/2$. The section ends with the following question (v2, p. 10, `ti_pra_07.tex`, lines 676–701, quotation at line 701).

> In summary, we have seen that  orthogonal  testers  are always maximally incompatible.   It is an open problem whether maximally incompatible testers must be orthogonal.

The finite-dimensional converse is the subject of the §V.C preregistration and its own dossier. The question above about canonical POVM robustness concerns §VI.C. [Preregistration #24241](https://github.com/the-omega-institute/trureturing/issues/24241) · [§V.C dossier](../../Problems/sedlak-reitzner-chiribella-ziman-2016-maximal-tester-orthogonality.md)

## Effect-weighted bound

For finite testers with normalization states $\rho,\sigma$, let $a=\sum_j\|A_j\|_\infty$, $b=\sum_k\|B_k\|_\infty$, and $\delta=\operatorname{Re}\operatorname{tr}(\rho\sigma)$. The effect-weighted positive joint cover gives $R_{\mathrm t}\leq 1-(2-\delta^2/(a+b))^{-1}$. Proportional splitting preserves the sums of norms. The proof extends the joint-cover construction in the project and uses the tester model from the cited article.
