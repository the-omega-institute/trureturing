---
bibkey: liutakagilloyd2019diagonaldiscord
authors: Zi-Wen Liu; Ryuji Takagi; Seth Lloyd
year: 2019
title: "Diagonal quantum discord"
doi: 10.1088/1751-8121/ab0774
url: https://arxiv.org/abs/1708.09076v2
claim: "Diagonal discord is the relative-entropy distance of a bipartite state from its pinching pi_A in the eigenbasis of the A marginal. The paper classifies local discord-nongenerating operations into mixed-unitary, isotropic and semiclassical channels, studies which local operations commute with pi_A, derives a qubit criterion for mixed-unitary channels, and conjectures that for qubits exactly the isotropic channels commute with pi_A, so that non-isotropic qubit mixed-unitary channels all fail the commutation condition."
strata_touched:
  - D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation
license: citation-only
triage: anchor
---

# Liu, Takagi and Lloyd, Diagonal quantum discord

Z.-W. Liu, R. Takagi and S. Lloyd, arXiv:1708.09076v2 [quant-ph]; J. Phys. A: Math. Theor. 52(13), 135301 (2019). Quotations are from the v2 TeX source, with the source's macros `\ee` (the channel $\mathcal E$) and `\change{…}` (a revision marker) expanded.

The channel classes of Section 3.2 ("Classification of discord nongenerating local operations"):

> Mixed-unitary channels ({\bf MU}): $\mathcal{E}^{\mathrm{MU}}(\rho) = \sum_\mu p_\mu U_\mu \rho U_\mu^\dagger$, where $\{p_{\mu}\}$ is a probability distribution ($p_{\mu}\in[0,1],\sum_\mu p_\mu=1$) and $U_{\mu}$ are unitary channels.

> Isotropic channels ({\bf ISO}): $\mathcal{E}^{\mathrm{ISO}}(\rho) = (1-\gamma)W(\rho) + \gamma I/d$, where $\gamma\in[0,1]$, $d$ denotes the dimension of the Hilbert space so $I/d$ is the maximally mixed state, and $W$ is either unitary or antiunitary.

The paper assumes the $A$ marginal nondegenerate ("For simplicity, $\rho_A$ is assumed to be nondegenerate.") and writes $X_A(\pi_A)$ for the local operations on $A$ that commute with the pinching $\pi_A$. After Lemma `qubitcondition`, which gives a criterion for a qubit mixed-unitary channel to lie in $X_A(\pi_A)$, it states:

> We conjecture (which is not important for our current purpose) that ${\bf ISO} = X_A(\pi_A)$. That is, qubit mixed-unitary channels that are not isotropic all fail to satisfy the condition.

## Verified locator

Source: https://arxiv.org/abs/1708.09076v2
- DOI: https://doi.org/10.1088/1751-8121/ab0774 (J. Phys. A: Math. Theor. 52(13), 135301; published 1 March 2019; title, authors, journal, volume, issue and page from Crossref).
- URL: https://arxiv.org/abs/1708.09076v2. The e-print is a gzipped tar archive; its member `revised_jphysa_clean.tex` has 1479 lines and md5 `3ae0def434187ebe1875d87961e23048`. Locations:
  - Subsection "Theory of discord destroying map $\pi$ and the monotonicity of diagonal discord", l. 318; the channel classes, l. 324–329; the nondegeneracy assumption, l. 339;
  - Subsubsection "$\pi$-commuting local operations and monotonicity", l. 345; Lemma `qubitcondition`, l. 354;
  - the conjecture, l. 463.
- The arXiv record lists v1 (30 August 2017) and v2 (25 February 2019) and the journal reference "J. Phys. A: Math. Theor. 52, 135301 (2019)" (arXiv API metadata).
