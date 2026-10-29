---
bibkey: rexitioskoueimancini2024bayesianfeedback
authors: Milajiguli Rexiti; Samad Khabbazi Oskouei; Stefano Mancini
year: 2024
title: "On the effectiveness of Bayesian discrete feedback for quantum information reclaiming"
doi: 10.1007/s11128-024-04467-x
url: https://arxiv.org/abs/2402.18941v1
claim: "A channel is measured on its environment through a Kraus decomposition and each outcome is corrected by the inverse of the unitary part of its Kraus operator, giving entanglement fidelity (1/d^2) sum_x (tr|T_x|)^2. For two uses of the channel, Markovian feedback corrects each step independently and Bayesian feedback corrects the accumulated branch; their fidelities involve tr(|T2||T1|) and tr|T2|T1||. The paper finds no Bayesian advantage for qubit channels and for the qutrit dephasing channel, an advantage for the qutrit amplitude damping channel, and asks for other examples of channels where Bayesian feedback is more effective."
strata_touched:
  - D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage
license: citation-only
triage: anchor
---

# Rexiti, Oskouei and Mancini, Bayesian discrete feedback for quantum information reclaiming

M. Rexiti, S. Khabbazi Oskouei and S. Mancini, arXiv:2402.18941v1 [quant-ph]; Quantum Information Processing 23(7), 258 (2024). Quotations are from the v1 TeX source, with the source's macros `\cal` and `\tr` kept as written.

Section 2 corrects each Kraus outcome $T_x=V_x|T_x|$ by $V_x^\dagger$ and measures the result by the entanglement fidelity

> $$F({\cal T}_{corr})=\frac{1}{d^2}\sum_x \left( \tr |T_x|\right)^2.$$

For two steps with Kraus decompositions $\{T^{(1)}_{x_1}\}$ and $\{T^{(2)}_{x_2}\}$ of the same channel, the Markovian and Bayesian strategies give

> $$F({\cal T}_{\rm corr} \circ {\cal T}_{\rm corr})=\frac{1}{d^2}\sum_{x_1,x_2} \left( {\rm tr} \left|{T}^{(2)}_{x_2}\right|\, \left|{T}^{(1)}_{x_1}\right| \right)^2,\qquad F\left(\left({\cal T} \circ {\cal T}_{\rm corr}\right)_{\rm corr}\right)=\frac{1}{d^2}\sum_{x_1,x_2} \left( {\rm tr} \left| {T}^{(2)}_{x_2} \, \left| {T}^{(1)}_{x_1}\right|\right| \right)^2,$$

and the comparison uses the optimal Kraus decomposition at each step. Section 4 finds no Bayesian advantage for the qutrit dephasing channel and an advantage for the qutrit amplitude damping channel.

The conclusion lists open problems:

> There are a number of problems that this study poses in future perspective. First, find other examples of channels for which Bayesian feedback is more effective than Marokovian one. Then, for these channels see if by increasing the dimension the advantage increases.

## Verified locator

Source: https://arxiv.org/abs/2402.18941v1
- DOI: https://doi.org/10.1007/s11128-024-04467-x (Quantum Information Processing 23(7), article 258; published 28 June 2024; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2402.18941v1. The e-print member `EffOfBayesianFB.tex` has 1001 lines and md5 `aeee6c3398ec2e49e99d0f461ed53290`. Locations:
  - the feedback model and the one-step fidelity, l. 118–152;
  - the two-step Markovian and Bayesian fidelities, l. 234–253; the optimal decompositions at each step, l. 286–297;
  - qubit channels, l. 333; the qutrit dephasing and amplitude damping channels, l. 675–903;
  - the open problems, l. 910–915.
