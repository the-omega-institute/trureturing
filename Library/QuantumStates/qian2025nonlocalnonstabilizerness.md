---
bibkey: qian2025nonlocalnonstabilizerness
authors: Dongheng Qian; Jing Wang
year: 2025
title: "Quantum non-local nonstabilizerness"
doi: 10.1103/PhysRevA.111.052443
url: https://arxiv.org/abs/2502.06393v4
claim: "Appendix F conjectures that some separable multi-qubit states cannot be brought into STAB by local unitaries. Appendix C derives the density (C5) of the non-local nonstabilizerness of Haar-random two-qubit pure states and leaves the closed form of its mean ȳ = ∫ yP(y)dy open, reporting ȳ ≈ 0.1917."
strata_touched:
  - D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction
  - D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1103/PhysRevA.111.052443

Source: https://arxiv.org/abs/2502.06393v4

Crossref identifies Dongheng Qian and Jing Wang, *Quantum nonlocal nonstabilizerness*, Physical Review A **111**, 052443 (2025), at this DOI. The arXiv title includes the hyphen in “non-local”.

Appendix F, PDF p. 8, states:

> However, we are unaware of any proof guaranteeing that every separable multi-qubit state can be transformed into a state belonging to STAB using only local unitary transformations, and we conjecture that this is not the case.

On the same page, equation (F1) is introduced by:

> A separable state is defined as the convex hull of pure product states [1]:

The distinction between STAB and STAB₀ is explicit. The sentence preceding (F2) says:

> while STAB is defined as the convex hull of pure stabilizer states:

Equation (F2) is

$$
\mathrm{STAB}:=\left\{\rho\;\middle|\;\rho=\sum_i p_i |\psi_i\rangle\langle\psi_i|\right\},
$$

followed by:

> where ψᵢ are pure stabilizer states.

The probabilities are nonnegative and sum to one, as specified by the convex-hull definition. Equation (F4) gives the numerical example

$$
\rho_0=\frac12|\phi_0\phi_0\rangle\langle\phi_0\phi_0|
       +\frac12|00\rangle\langle00|,
\qquad
|\phi_0\rangle=\cos(\pi/8)|0\rangle+\sin(\pi/8)|1\rangle.
$$

The source reports the numerical local-unitary minimum $\mathcal M_R(\rho_0)\approx0.0703$. This reported decimal is not an exact certificate. The conjecture concerns the full convex stabilizer hull STAB, rather than the smaller set STAB₀ of normalized commuting-Pauli subgroup projectors.

## The Haar mean of Appendix C

§III, PDF p. 3, states:

> While the analytical expression for this probability distribution can be derived in Appendix C, a closed-form expression for the average value of M, analogous to that for entanglement [68, 69], remains unclear. Nevertheless, numerical results suggest that the average M is approximately 0.192.

Appendix C, PDF pp. 6–7, uses the Haar distribution P(x) = 3(1 − 2x)² of the Schmidt weight x = cos²θ, and the two-qubit formula

$$
M(x)=\ln\frac{8}{7+\cos 8\theta}=\ln\frac{1}{1+4x(x-1)(1-2x)^2}. \tag{C1}
$$

It derives the density of y = M(x), with z ≡ √(4 − 3e^y):

$$
P(y)=\frac{3e^{-y/2}}{4z\sqrt{2(e^y-1)}}\Big[(e^{y/2}+z)\sqrt{1-e^{-y/2}z}+(e^{y/2}-z)\sqrt{1+e^{-y/2}z}\Big], \tag{C5}
$$

and then states:

> However, we have not been able to find a simple closed-form expression for the average amount of NN, ȳ ≡ ∫ yP(y)dy, for the Haar random state. Consequently, we numerically integrate the expression, which yields an approximate value of ȳ ≈ 0.1917.
