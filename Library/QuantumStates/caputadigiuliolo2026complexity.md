---
bibkey: caputadigiuliolo2026complexity
authors: Pawel Caputa, Giuseppe Di Giulio, Tran Quang Loc
year: 2026
title: "Complexity Inequalities for Quantum Subsystems"
doi: 10.48550/arXiv.2606.20790
url: https://arxiv.org/abs/2606.20790v2
claim: 'Based on all the examples discussed in this manuscript, we conjecture that $\left(b_n^{(A)}\right)^2>0$ for every $n$, and hence that all the coefficients $b_n^{(A)}$ are real.'
strata_touched:
  - D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2606.20790

DOI URL: https://doi.org/10.48550/arXiv.2606.20790

Source: https://arxiv.org/abs/2606.20790v2

PDF: https://arxiv.org/pdf/2606.20790v2

The conjecture appears in §3.1, printed p. 15 (PDF page 16), in v2.
The source TeX is `SubsystemComplexity_Draft_v0.tex`.

> At present, however, we are unable to establish the sign of $\left(b_n^{(A)}\right)^2$ in full generality. Based on all the examples discussed in this manuscript, we conjecture that $\left(b_n^{(A)}\right)^2>0$ for every $n$, and hence that all the coefficients $b_n^{(A)}$ are real.

The normalized subsystem overlap is defined by

$$
R_A(t)=\frac{\textrm{Tr}\left(\rho_A(t)\rho_A(0)\right)}{\textrm{Tr}\left(\rho^2_A(0)\right)}.
$$

The moment convention and the first squared coefficient are

$$
\mu_n^{(A)}=\partial_t^n R_A(t)\big\vert_{t=0},
\qquad
\left(b_1^{(A)}\right)^2=
\left(\mu_1^{(A)}\right)^2-\mu_2^{(A)}.
$$

Their TeX labels are `generaldef_RL`, `subsystem moments` and
`b1_generalprocedure`; the v2 PDF numbers them (3.2), (3.3) and (3.5),
on printed pp. 14–15. The full pure state evolves as
$|\psi(t)\rangle=e^{-{\rm i}Ht}|\psi(0)\rangle$ under a time-independent
Hermitian Hamiltonian, and $\rho_A(t)$ is its partial trace over $B$.

Appendix C.1.1 establishes the restricted nonnegative conclusion
$\left(b_1^{(A)}\right)^2\ge 0$ when
$[\rho_A(0)\otimes 1_B,\rho(0)]=0$, including product initial states.
This is distinct from strict positivity for all states and Hamiltonians.
