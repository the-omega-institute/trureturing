---
bibkey: negari2026gaussianapproximation
authors: Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert
year: 2026
title: "Approximation theorems for fermionic Gaussian states"
doi: 10.48550/arXiv.2610.01860
url: https://arxiv.org/abs/2610.01860v1
claim: "Section VI asks whether the constants in the high-degree energy and free-energy estimates are optimal."
strata_touched:
  - D5/S3/Quantum/Fermionic/FockMajoranaCarrier
  - D5/S3/Quantum/Fermionic/ConferenceMatrices
  - D5/S3/Quantum/Fermionic/CompleteCartesianGraph
  - D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum
  - D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian
  - D5/S3/Quantum/Fermionic/CoordinateAverage
  - D5/S3/Quantum/Fermionic/JointSignProjectors
  - D5/S3/Quantum/Fermionic/FlatCliffordGround
  - D5/S3/Quantum/Fermionic/CliffordGroundDensity
  - D5/S3/Quantum/Fermionic/PhysicalSiteProducts
  - D5/S3/Quantum/Fermionic/GibbsProductGap
  - D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness
license: citation-only
triage: anchor
---

# Approximation theorems for fermionic Gaussian states

Section VI, printed page 26, states:

> It remains open, however, whether the constants in the resulting high-degree energy and free-energy estimates are optimal, since their derivation also uses edge averaging, Cauchy–Schwarz, and only the operator-norm normalization of the interactions.

The estimates are Theorem III.1, equation (44), and Theorem III.5,
equation (79). Both have bound $\sqrt{2m/D}$ for a finite simple
$D$-regular graph with $m$ fermionic modes per vertex and $D\geq1$.
The Hamiltonian is the edge average
$H=|E|^{-1}\sum_{e\in E}H_e$, with real quadratic inter-site Majorana
coefficients and operator norm $\|H_e\|\leq1$.

The Majorana convention is
$\gamma_{2j-1}=c_j+c_j^\dagger$ and
$\gamma_{2j}=i(c_j-c_j^\dagger)$.
Physical density matrices satisfy $[\rho,P]=0$, where
$P=(-1)^{\widehat N}$ is number parity.

The energy comparison minimizes $\operatorname{tr}(H\rho)$ over physical
density matrices and over physical product density matrices. The free-energy
comparison uses the actual Gibbs density
$\rho_\beta=e^{-\beta H}/\operatorname{tr}(e^{-\beta H})$ and the tensor
product $\sigma_\beta$ of its one-site partial traces, with
$F_\beta(\omega)=\operatorname{tr}(H\omega)-S(\omega)/\beta$ and
$S(\omega)=-\operatorname{tr}(\omega\log\omega)$ in nats.

Uniform optimality of the prefactor does not require equality at every
degree or at any finite inverse temperature. These are distinct questions.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2610.01860
- Source: https://arxiv.org/abs/2610.01860v1

Pages 3–4 fix the carrier and operators:

> The number operator and parity operator are given by

$\widehat N=\sum_{j=1}^m c_j^\dagger c_j$, $P=(-1)^{\widehat N}$.

> From the creation and annihilation operators we define Hermitian Majorana operators by

$\gamma_{2j-1}=c_j+c_j^\dagger$, $\gamma_{2j}=i(c_j-c_j^\dagger)$, $j=1,\ldots,m$.

> They satisfy the Clifford relations

$\{\gamma_p,\gamma_q\}=2\delta_{p,q}\mathbf 1$, $\gamma_p^\dagger=\gamma_p$.

> Physical fermionic states obey the parity superselection rule

$[\rho,P]=0$. The Lean reading of the operator power is fixed by preregistration
[#15127](https://github.com/the-omega-institute/trureturing/issues/15127).
