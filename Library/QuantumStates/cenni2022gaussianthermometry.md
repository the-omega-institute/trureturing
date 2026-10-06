---
bibkey: cenni2022gaussianthermometry
authors: M. F. B. Cenni; L. Lami; A. Acín; M. Mehboudi
year: 2022
title: "Thermometry of Gaussian quantum systems using Gaussian measurements"
doi: null
url: https://arxiv.org/abs/2110.02098v4
claim: "Section 3.2, Eq. (47), conjectures that for product thermal states the optimal joint Gaussian measurement has the same Fisher information as the optimal local measurement."
strata_touched:
  - D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation
license: citation-only
triage: anchor
---

# Thermometry of Gaussian quantum systems using Gaussian measurements

M. F. B. Cenni, L. Lami, A. Acín and M. Mehboudi, arXiv:2110.02098v4 (2022).

Page 6, §3.2.2, Eq. (36), defines the zero-displacement Gaussian-measurement Fisher information by

> "${\cal F}^{\rm C}({\bm \sigma};{\bm \sigma}_s^{M}) \equiv {\cal F}^{\rm C}({\bm 0},{\bm \sigma};{\bm \sigma}_s^{M})$" and "${\cal F}^{\rm C}({\bm d},{\bm \sigma};{\bm \sigma}_s^{M}) = \partial_{T} {\bm d}^{T}({\bm \sigma} + {\bm \sigma}_s^{M})^{-1}\partial_{T}{\bm d} + \frac{1}{2}\Tr \left[\left(({\bm \sigma} + {\bm \sigma}_s^{M})^{-1} \partial_{T}{\bm \sigma}\right)^2 \right]$."

For a thermal mode the paper writes

> "If the state is at thermal equilibrium, then $\nu = \coth(\omega/2T)$."

The open statement in §3.2, Eq. (47), is quoted verbatim:

> "${\cal F}^{\rm C}(\oplus_k {\bm \sigma}_{k}; {\bm \sigma}^M_{\max}) \overset{?}{=} {\cal F}^{\rm C}(\oplus_k {\bm \sigma}_{k}; \oplus_k{\bm \sigma}_{k,\max}^M)$"

> "Based on these observations we conjecture this is generally true, however, a rigorous proof is missing currently."

The formal encoding uses `D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.coth`, `thermalNuDeriv`, `thermalCov`, `thermalCovDeriv`, `IsGaussianMeasurementCov`, `fisherC`, `localCov`, `localFisher`, and `claim` in the refutation module. The two-mode certificate uses T = 1, frequencies `(ln 3, 2 ln 3)` (encoded equivalently as `(2 artanh(1/2), 4 artanh(1/2))`), and the explicit symplectic covariance from the module.

## Verified locator

- arXiv: https://arxiv.org/abs/2110.02098v4, p. 6 §3.2.2, Eq. (36); §3.2, Eq. (47), source version 2022-06-27.
