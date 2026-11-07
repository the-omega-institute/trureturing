---
bibkey: ducuarasusaskrzypczyk2024hidden
authors: Andrés F. Ducuara, Cristian E. Susa, Paul Skrzypczyk
year: 2024
title: "Locally inaccessible hidden quantum correlations"
doi: 10.1103/PhysRevA.110.022435
url: https://arxiv.org/abs/2406.03945v1
claim: "The paper proves, modulo a conjecture on quantum steering ellipsoids, the existence of two-qubit states whose hidden CHSH and F3 violations cannot be revealed by local filters on one side only; the conjecture states that the maximal CHSH and F3 violations are bounded by functions of the steering-ellipsoid centre length alone, with numerically estimated impossibility thresholds 0.5 and 0.66."
strata_touched:
  - D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold
license: citation-only
triage: anchor
---

# Ducuara–Susa–Skrzypczyk, locally inaccessible hidden quantum correlations

## Verified locator

DOI: 10.1103/PhysRevA.110.022435

Source: https://arxiv.org/abs/2406.03945v1

Phys. Rev. A 110, 022435 (2024), published 26 August 2024.

A. F. Ducuara, C. E. Susa and P. Skrzypczyk, arXiv:2406.03945v1 [quant-ph] (6 June 2024, the only version), source file `QC_LI.tex`.

## Statement

For a two-qubit state $\rho$ with Bloch vectors $\boldsymbol a$, $\boldsymbol b$ and correlation matrix $T_{ij}=\operatorname{tr}[\rho\,\sigma_i\otimes\sigma_j]$, the maximal violation of the $\mathrm F_3$ steering inequality is $\mathrm F_3(\rho)=\sqrt{s_1^2+s_2^2+s_3^2}$, with $s_i$ the singular values of $T$ (Eq. (CAC), l. 211), and Bob's steering-ellipsoid centre is $\boldsymbol c_B=\gamma_a^2(\boldsymbol b-T^{\mathsf T}\boldsymbol a)$ with $\gamma_a=(1-a^2)^{-1/2}$ (Eq. (QSEcentre), l. 261). The paper states (l. 282–288):

> **Conjecture (QSE conjecture).** For any two-qubit state $\rho$, its maximal violation of the CHSH-inequality and the $\rm F_3$-inequality are upper bounded by functions that depend on the magnitude of the QSE's centre as ${\rm B}(\rho)\le f_{\rm CHSH}(c_B)$ and ${\rm F_3}(\rho)\le f_{\rm F_3}(c_B)$, respectively.

> Exploring the form of function $f_{\rm F_3}(c_B)$ is an interesting task which we leave for future research. … there seem to exist values $c_{\rm CHSH}=0.5$ and $c_{\rm F_3}=0.66$, such that states with QSE centres' magnitudes greater than these values, can no longer lead to a violation of the CHSH-inequality and the $\rm F_3$-inequality, respectively.

The CHSH half restates Conjecture 1 of Milne, Jennings, Jevtic and Rudolph (2014).

## Encoding and boundary

The repository defines $\mathrm F_3(\rho)$ as the supremum of $\frac1{\sqrt3}\big|\sum_i\operatorname{tr}[\rho\,(\boldsymbol\alpha^i\cdot\boldsymbol\sigma)\otimes(\boldsymbol\beta^i\cdot\boldsymbol\sigma)]\big|$ over unit vectors $\boldsymbol\alpha^i$ and orthonormal frames $\boldsymbol\beta^i$, and uses Bob's centre with the convention $\boldsymbol c_B=\boldsymbol b$ when $|\boldsymbol a|=1$. It proves $\mathrm F_3(\rho)\le\max\{\sqrt{3(1-c_B)},1\}$ for every two-qubit density matrix and exhibits, for every $0\le t<\tfrac23$, a state with $c_B=t$ and $\mathrm F_3>1$; the impossibility threshold is therefore exactly $\tfrac23$. The optimal envelope of $\mathrm F_3$ at fixed centre length, the CHSH half and the hidden and one-sided-filter quantities are outside this conclusion.
