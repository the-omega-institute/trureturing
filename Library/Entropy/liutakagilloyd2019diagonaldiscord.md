---
bibkey: liutakagilloyd2019diagonaldiscord
authors: Zi-Wen Liu; Ryuji Takagi; Seth Lloyd
year: 2019
title: "Diagonal quantum discord"
doi: 10.1088/1751-8121/ab0774
url: https://arxiv.org/abs/1708.09076v2
claim: "Diagonal discord is the minimum entropy gain of pinching a bipartite state in an eigenbasis of the measured marginal. Conjecture 1 asserts monotonicity under local discord-nongenerating operations on the measured qubit. A separate conjecture concerns the isotropic characterization of channels that commute with the marginal pinching."
strata_touched:
  - D5/S3/Quantum/Information/DiagonalDiscordMonotonicity
  - D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation
license: citation-only
triage: anchor
---

# Liu, Takagi and Lloyd, Diagonal quantum discord

Z.-W. Liu, R. Takagi and S. Lloyd, arXiv:1708.09076v2 [quant-ph]; J. Phys. A: Math. Theor. 52(13), 135301 (2019). Quotations are from the v2 TeX source, with the source's macros `\ee` (the channel $\mathcal E$) and `\change{…}` (a revision marker) expanded.

## Conjecture 1

The journal version states the conjecture in §3.2.2, p. 9, and arXiv v2 states it in §III.B.2, p. 6. The quantity in eqs. (2) and (8) minimizes over all rank-one eigenbasis pinchings of the measured marginal, including choices inside degenerate eigenspaces. The theorem `diagonalDiscord_localChannel_mono_attained` gives the comparison of attained minima for every finite bipartite state under a local CPTP channel preserving classical–quantum states. The statement includes singular states and every finite measured dimension. [Journal](https://doi.org/10.1088/1751-8121/ab0774) · [arXiv v2, p. 6](https://arxiv.org/pdf/1708.09076v2#page=6)

The fixed-pinching relative-entropy decomposition used in the proof appears in Gour, Marvian and Spekkens, *Measuring the quality of a quantum reference frame*, Theorem 3 and eqs. (9)–(15). The closest-reference formula visible in the publisher's index for Chruściński and Matsuoka, *Quantum Conditional Probability and Measurement Induced Disturbance of a Quantum Channel*, concerns a related same-marginal comparison. Their full text was unavailable for comparison. The checked sources yielded no earlier proof of Conjecture 1. [Gour–Marvian–Spekkens, arXiv v2](https://arxiv.org/abs/0901.0943v2) · [Chruściński–Matsuoka](https://doi.org/10.1016/S0034-4877(20)30060-4)

## Separate commutation conjecture

The mixed-unitary commutation result addresses the unnumbered conjecture on the same page as Conjecture 1. [PR #23228](https://github.com/the-omega-institute/trureturing/pull/23228)

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
