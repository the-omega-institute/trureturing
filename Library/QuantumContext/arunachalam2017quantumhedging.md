---
bibkey: arunachalam2017quantumhedging
authors: Srinivasan Arunachalam; Abel Molina; Vincent Russo
year: 2018
title: "Quantum hedging in two-round prover-verifier interactions"
doi: 10.4230/LIPIcs.TQC.2017.5
url: https://arxiv.org/abs/1310.7954v5
claim: "For a two-round game in which Bob returns one half of an entangled two-qubit state to Alice for a projective measurement, the paper characterizes when Bob can win at least one of n parallel repetitions with certainty, and suggests from numerical evidence that Bob cannot perfectly hedge more than n/2 of the games."
strata_touched:
  - D5/S3/Quantum/Information/HedgingMajorityThreshold
license: citation-only
triage: anchor
---

# Quantum hedging in two-round prover-verifier interactions

Srinivasan Arunachalam, Abel Molina and Vincent Russo, arXiv:1310.7954v5 (quant-ph), 2017-03-12, first version 2013-10-29; published in TQC 2017, LIPIcs 73 (2018) 5:1–5:30. Quotations are from the v5 TeX source.

The game (Section 3):

> Alice prepares the 2-qubit state $\rho_{\alpha} = u_\alpha u_{\alpha}^* \in \Density(\X \otimes \Z)$ in registers $(\reg{X},\reg{Z})$ where

> u_{\alpha} = \alpha \ket{00} + \sqrt{1 - \alpha^2} \ket{11} \in \X \otimes \Z,

> Bob applies a channel $\Phi \in \Channel(\X,\Y)$ to the contents of $\reg{X}$. This results in a state $\sigma \in \Density(\Y \otimes \Z)$, contained in registers $(\reg{Y},\reg{Z})$. Register $\reg{Y}$ is sent back to Alice.

> P_{1,\theta} = v_{\theta} v_{\theta}^*, ~P_{0,\theta} = \I - P_{1,\theta},   \nonumber \\
> v_{\theta} = \cos(\theta) \ket{00} + \sin(\theta) \ket{11} \in \Y \otimes \Z.

> An outcome of ``0'' or ``1'' denotes a losing or winning outcome for Bob, respectively.

Parallel repetition (Section 3):

> \Phi_n \in \Channel(\X_1 \otimes \cdots \otimes \X_n, \Y_1 \otimes \cdots \otimes \Y_n).

The open question (Section 5):

> However, it still remains open to determine the conditions under which Bob can always win at least $k$ out of $n$ repetitions for some $k > 1$.

> Based on our current numerical evidence, it is possible that Bob cannot perfectly hedge more than $k = n/2$ games.

## Verified locator

- URL: https://arxiv.org/abs/1310.7954v5 (v5, 2017-03-12; source `arxiv_v5.tex`, md5 `78b99144eee8f68c949b2319e53fee68`): the game (l. 196–209), parallel repetition (l. 211–220), and the open question (l. 574).
- DOI: 10.4230/LIPIcs.TQC.2017.5 (TQC 2017). The published text was not read.
