---
bibkey: memarzadeh2016minimum
authors: Laleh Memarzadeh; Stefano Mancini
year: 2016
title: "Minimum output entropy of a non-Gaussian quantum channel"
doi: 10.1103/PhysRevA.94.022341
url: https://arxiv.org/abs/1605.04525v1
claim: "Conjecture 1: truncated loss-dephasing minimum output entropy is attained by a binomial or kappa state."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation
license: citation-only
triage: anchor
---

# Truncated loss-dephasing minimum output entropy

Conjecture 1, section IV, arXiv v1 PDF p. 4:

> In a truncated Hilbert space of dimension K+1, the minimal output entropy of the quantum channel (3) is achieved either by binomial states of Eq.(14) or by states |κ_α⟩ of Eq. (11), depending on the values of ε and t.

The defining channel equations (1)–(7), pp. 1–2, give

$$\frac{d\rho}{dt}=(1-\epsilon)\mathcal L_{AD}(\rho)+\epsilon\mathcal L_{PD}(\rho),\qquad
\Phi_{\epsilon,t}(\rho)=\sum_{j,k=0}^{\infty} A_jP_k\rho P_k^\dagger A_j^\dagger,$$

$$A_j=\sum_{l=j}^{\infty}\sqrt{\binom lj}(1-f)^{(l-j)/2}f^{j/2}|l-j\rangle\langle l|,
\quad f=1-e^{-2(1-\epsilon)t},$$

$$P_k=\sum_{l=0}^{\infty}\sqrt{\frac{(2l^2\epsilon t)^k}{k!}}e^{-l^2\epsilon t}|l\rangle\langle l|.$$

Equation (9) fixes the input energy, $\operatorname{Tr}(\rho a^\dagger a)=N$.
Equation (11) defines
$|\kappa_\alpha\rangle=\sqrt{1-N/K}|0\rangle+\sqrt{N/K}e^{i\alpha K}|K\rangle$.
Equation (14) defines the binomial amplitudes
$\beta_n=\sqrt{\binom Mn\mu^n(1-\mu)^{M-n}}$; the energy condition is $M\mu=N$,
and the allowed truncation sizes satisfy $\lceil N\rceil\le M\le K$.

The Lean encoding uses matrices on `Fin (K+1)`, the Kraus equations above,
and positive semidefinite trace-one inputs with number expectation N. For K ≥ 1,
N ∈ [0,K], ε ∈ [0,1], and t ≥ 0, the claim says that some binomial or κ candidate
has output entropy no greater than every admissible input. Its negation is proved.
The spectral entropy uses natural logarithms, whereas the paper uses base two;
multiplication by the positive constant 1/log(2) preserves the ordering.
The definition extends entropy to all raw matrices by assigning zero to
non-Hermitian matrices; the matrices used in the refutation are Hermitian and positive.

The counterexample uses K=2, N=3/2, ε=6/7, t=(7/2)log(2), and
ψ=(|1⟩+|2⟩)/√2. Its output spectrum has a value above 1/2 and a value below 1/8.
The only admissible binomial candidate is M=2, μ=3/4; its output spectrum and
every κ candidate's output spectrum lie strictly between 1/8 and 1/2.
Their common trace is one. Strict three-coordinate majorization gives smaller
entropy for ψ than for every candidate; no assertion that ψ is the global minimizer is made.

The displayed κ output in section III uses $(1-f)^K$ in its off-diagonal
coefficient. The defining Kraus equations give $(1-f)^{K/2}$ instead.
The encoding follows the Kraus equations and derives the K=2 off-diagonal
coefficient √3/32768 at the counterexample parameters.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.94.022341
- URL: https://arxiv.org/abs/1605.04525v1
- PDF: https://arxiv.org/pdf/1605.04525v1 (channel pp. 1–2; Conjecture 1 p. 4).
