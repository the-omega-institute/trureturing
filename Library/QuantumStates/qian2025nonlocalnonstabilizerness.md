---
bibkey: qian2025nonlocalnonstabilizerness
authors: Dongheng Qian; Jing Wang
year: 2025
title: "Quantum non-local nonstabilizerness"
doi: 10.1103/PhysRevA.111.052443
url: https://arxiv.org/abs/2502.06393v4
claim: "Appendix F conjectures that some separable multi-qubit states cannot be brought into STAB by local unitaries."
strata_touched:
  - D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction
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
