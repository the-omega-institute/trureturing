---
bibkey: sieniawski2026adaptivechannel
authors: Stanisław Sieniawski and Rafał Demkowicz-Dobrzański
year: 2026
title: Adaptive quantum channel discrimination using methods of quantum metrology
doi: 10.1088/1367-2630/ae3edd
url: https://arxiv.org/abs/2510.15506v3
claim: "Equation (39) defines longitudinal dephasing with phase encoding. Sections IV.1 and V.4 give metrological bounds and numerical discrimination results."
strata_touched:
  - D5/S3/Quantum/ProcessReconstruction/TwoQueryPhaseDiscrimination
  - D5/S3/Quantum/ProcessReconstruction/ThreeQueryPhaseProtocol
license: citation-only
triage: anchor
---

# Longitudinal dephasing discrimination

The two Kraus operators in Eq. (39) give the complex coherence multiplier
((2p-1)e^{-i	heta}). A common known rotation centers the two phase
hypotheses. In the centered pair the real coherence is shared and the
imaginary coherences have opposite signs.

The two-query proof writes each centered dwell as a complementary mixture
of the same two diagonal unitaries. The two independent mixed-label paths
occur with the same probabilities in both hypotheses, so they cancel in
the output difference for any common control. The remaining unitary
comparison has an explicit attaining pure two-qubit probe.

## Verified locator

[ArXiv v3 abstract](https://arxiv.org/abs/2510.15506v3).
[Equation (39) and Section V.4](https://arxiv.org/html/2510.15506v3#S5.E39).
[Published article](https://doi.org/10.1088/1367-2630/ae3edd).
[Two-hypothesis unitary bound in Ito and Mori, Theorem 1](https://arxiv.org/html/2107.03948v2).

The three-use theorem exhibits a pair of longitudinal-dephasing channels
whose coherences are $3/4\pm 5i/16$. For normalized pure parallel probes
with arbitrary finite auxiliary memory, the trace distance of the two
outputs is at most $2159137/4000000$. The constructed common isometric
control achieves a trace distance of at least $88529493/163840000$.
The lower bound on their difference is $2281037/4096000000$.

The proof contracts the output test to path Gram matrices, verifies
positive semidefinite dual slacks by rational factorizations, and
realizes the adaptive Gram matrix using positive square roots.
The source paper gives numerical longitudinal-dephasing benchmarks in
Section V.4 and discusses the strategy hierarchy in Section VI. The constructive finite-use separation here is a
repository derivation for the channel model of Eq. (39).
The exact adaptive optimum remains open. The searched sources leave priority for this specific pair undetermined.

[arXiv:2510.15506v3, Section VI](https://arxiv.org/html/2510.15506v3#S6.p4).
