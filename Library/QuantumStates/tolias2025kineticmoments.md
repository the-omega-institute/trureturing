---
bibkey: tolias2025kineticmoments
authors: P. Tolias; T. Dornheim; J. Vorberger
year: 2025
title: "Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor"
doi: 10.1002/ctpp.70090
url: https://arxiv.org/abs/2508.17810v1
claim: "Therefore, our conjecture states that the following result holds for the interacting uniform electron gas M_{\\mathrm{S,KIN}}^{(2k+1)}(q)=\\left(\\frac{\\hbar{q}^2}{2m}\\right)^{2k+1}\\frac{1}{2k+2}\\sum_{i=0}^{k}\\binom{2k+2}{2i+1}\\left(\\frac{2}{\\hbar{q}}\\right)^{2i}\\langle{p}^{2i}\\rangle_{0}\\,, where $k$ is an arbitrary non-negative integer."
strata_touched:
  - D5/S3/Quantum/KineticMoments/IsotropicAverage
  - D5/S3/Quantum/KineticMoments/OddMoment
license: citation-only
triage: anchor
---

# Kinetic odd frequency moments

## Verified locator

DOI: https://doi.org/10.1002/ctpp.70090

Source: https://arxiv.org/abs/2508.17810v1

The locators refer to the arXiv v1 PDF: Sec. 2.2, Eq. (9), p. 3;
Sec. 2.3, Eqs. (16)–(17), p. 5; Sec. 2.4, pp. 5–6.
The journal locator is Contributions to Plasma Physics (2026), e70090.

Sec. 2.2, p. 3:

> The pure kinetic contribution to the odd dynamic structure factor frequency moments of arbitrary order is obtained from Eq.(4) by considering only the kinetic part of the Hamiltonian, i.e. setting $\hat{H}\equiv\hat{K}$.

Equation (9) splits the $2k+1$ commutator nests between the density operator
and its conjugate, with $\ell$ on the conjugate side. The kinetic Hamiltonian
is $\hat K=\sum_j |\hat{\boldsymbol p}_j|^2/(2m)$.

Sec. 2.3, p. 5:

> Therefore, our conjecture states that the following result holds for the interacting uniform electron gas

$$
M_{\mathrm{S,KIN}}^{(2k+1)}(q)=\left(\frac{\hbar{q}^2}{2m}\right)^{2k+1}\frac{1}{2k+2}\sum_{i=0}^{k}\binom{2k+2}{2i+1}\left(\frac{2}{\hbar{q}}\right)^{2i}\langle{p}^{2i}\rangle_{0}\,,
$$

> where $k$ is an arbitrary non-negative integer.

Equation (17) expresses the same assertion as a nested-commutator average.
Sec. 2.4 evaluates the orders $k=0,1,2,3$ directly.

## Momentum-space encoding and scope

The configuration carrier is `Fin N → EuclideanSpace ℝ (Fin 3)`.
The density operators sum pullbacks by the single-particle shifts
$\boldsymbol p_j\mapsto\boldsymbol p_j\pm\hbar\boldsymbol q$;
the kinetic operator multiplies by $\sum_j|\boldsymbol p_j|^2/(2m)$.
The commutator average is the integral of its proved multiplier against one
momentum-configuration probability measure. Its per-particle even moment is
$N^{-1}\sum_j\int|\boldsymbol p_j|^{2i}d\nu$.

Simultaneous determinant-$+1$ rotations preserve $\nu$, and integrability of
$|\boldsymbol p_j|^{2k}$ is a hypothesis for each particle. No independence,
exchangeability, fermionic symmetry or Gaussian law is imposed. The statement
constructs no thermodynamic-limit state, proves no finiteness of Coulomb
moments and asserts nothing about the full non-kinetic moment.
