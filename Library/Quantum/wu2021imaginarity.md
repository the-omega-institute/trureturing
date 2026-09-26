---
bibkey: wu2021imaginarity
title: Operational Resource Theory of Imaginarity
authors: Kang-Da Wu, Tulja Varun Kondra, Swapan Rana, Carlo Maria Scandolo, Guo-Yong Xiang, Chuan-Feng Li, Guang-Can Guo, Alexander Streltsov
year: 2021
url: https://arxiv.org/abs/2007.14847v2
doi: 10.1103/PhysRevLett.126.090401
claim: Relative to a fixed basis, the robustness of imaginarity equals half the trace norm of the difference between a state and its transpose; real operations admit real Kraus operators.
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed real structure and imaginarity

Wu et al., arXiv:2007.14847v2, dated 2 March 2021, define real states
relative to a specified basis and real operations through Kraus operators
with real entries. The setup on page 2 follows the resource theory of
Hickey and Gour, *Quantifying the imaginarity of quantum mechanics*,
Journal of Physics A **51**, 414009 (2018).

Theorem 2, equation (5), gives

$$
I_R(\rho)=\frac12\|\rho-\rho^{\mathsf T}\|_1,
\qquad
F_I(\rho)=\frac{1+I_R(\rho)}2.
$$

Here $I_R$ is the robustness defined in equation (4), and $F_I$ is the
maximal fidelity with a maximally imaginary qubit under real operations,
defined in equation (3). For a Hermitian density matrix,
$\rho^{\mathsf T}=\overline\rho$. The measure and identity are existing
results. They depend on the chosen real structure and are not lower
bounds over all changes of basis.

Theorem 1, equation (2), describes stochastic pure-state conversion under
real operations using $|\langle\psi^*|\psi\rangle|$. Neither theorem asserts
that an entire parameter-dependent preparation can be made real by one
fixed coordinate change. Nor do they determine the minimum dimension of
an exact programmable channel with prescribed Fisher-calibration and
curvature data.

The quantum-volume comparison concerns one fixed conjugation preserved
by every state of a preparation curve, while allowing an arbitrary CPTP
processor. Conjugating and averaging that processor is justified
separately by the target channel's conjugation covariance. A minimum
dimension gap additionally requires the channel-specific sharp-state
rigidity and continuation obstruction. A quantitative use of $I_R$
requires a lower bound derived from those constraints; the trace-norm
identity alone does not provide one.

This note paraphrases the cited definitions and theorem. No article PDF,
figure or extended excerpt is redistributed.
