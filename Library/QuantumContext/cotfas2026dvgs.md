---
bibkey: cotfas2026dvgs
authors: Nicolae Cotfas
year: 2026
title: Frame-dependent coherence of Gaussian quantum states
doi: 10.48550/arXiv.2610.05623
url: https://arxiv.org/abs/2610.05623v1
claim: "The uncertainty condition (11) suffices for positivity of the mixed discrete-variable Gaussian matrix in Eqs. (21)–(22)."
strata_touched:
  - D5/S3/Quantum/CotfasDVGS
license: citation-only
triage: anchor
---

# Cotfas discrete Gaussian positivity

## Verified locator

DOI: 10.48550/arXiv.2610.05623

Source: https://arxiv.org/abs/2610.05623v1

The cited version is v1. The covariance and continuous Wigner formulas are Eqs. (10)–(11), page 2; displaced parity is Eq. (18), page 2; the mixed discrete Gaussian and its lattice weights are Eqs. (21)–(22), page 3.

## Source statements

Page 2, Eq. (11): “where the covariance matrix σ = (σ11 σ12; σ12 σ22), satisfying σ + i(0 1; −1 0) ≥ 0, is a real 2×2 symmetric positive-definite matrix.”

Page 2: “an odd-dimensional (d = 2s + 1) space H_d, which we represent as the space of all the functions ψ : {−s, −s + 1, ..., s − 1, s} → C” and “the addition is modulo d.”

Page 2, Eq. (18): “Π̃(n, k)ψ(m) = e^{(4πi/d) k(m−n)} ψ(2n − m).”

Page 3, Eq. (21): “Mixed DVGS - Inspired by the formulas (17) and (20), we have introduced in [21], for any d = 3, 5, 7, ..., the discrete version ρ̃_σ = Σ_{n,k=−s}^{s} W̃_σ(n, k) Π̃(n, k).”

Page 3, after Eq. (22): “As concern ρ̃_σ, we do not know if (11) is sufficient in order to have ρ̃_σ ≥ 0. Based on our numerical investigations, we conjecture that this is true.”

## Mathematical scope

The continuous Wigner function is exactly Eq. (10), with real covariance inverse and determinant. The finite indices are the subtype of integers in Finset.Icc (−s) s. Centered reduction uses ZMod.valMinAbs modulo 2s+1; its integer value is the Euclidean remainder of x+s modulo 2s+1 minus s. Displaced parity is the matrix of the source's operator in this basis. The lattice weight is the signed infinite sum in Eq. (22), before normalization. The mixed matrix is the finite sum in Eq. (21), multiplied by the inverse of its complex trace.

The conclusion quantifies over s ≥ 1, h > 0 and every real positive-definite covariance satisfying (11). It states positive-semidefiniteness and trace one. It includes the determinant-one boundary. No necessity statement or separate dimension-one theorem is asserted.

The source explicitly conjectures positivity. The Gaussian Gram, Poisson summation and theta ingredients are classical; no originality of those ingredients is asserted. Literature completeness is ASSUMED-UNVERIFIED: the screen in issue #18946 did not exclude an equivalent result in the subscription-only main text of Feng–Luo, International Journal of Theoretical Physics 63, 40 (2024).
