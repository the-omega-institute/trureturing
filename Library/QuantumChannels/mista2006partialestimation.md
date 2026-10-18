---
bibkey: mista2006partialestimation
authors: Ladislav Mišta Jr., Jaromír Fiurášek
year: 2006
title: "Optimal partial estimation of quantum states from several copies"
doi: 10.1103/PhysRevA.74.022316
url: https://arxiv.org/abs/quant-ph/0606112
claim: "Introduction, Eq. (2): the conjectured optimal output-fidelity versus estimation-fidelity trade-off for N identical pure qudits, with one output qudit."
strata_touched:
  - D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral
  - D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff
license: citation-only
triage: anchor
---

# Optimal partial estimation from several identical pure states

## Verified locator

DOI: 10.1103/PhysRevA.74.022316
Source: https://arxiv.org/abs/quant-ph/0606112
Version read: https://arxiv.org/pdf/quant-ph/0606112v1
Published in Physical Review A 74, 022316.

## Source statement

Page 1, Introduction: "Moreover, we also conjecture that the optimal fidelity trade-off for an ensemble of N identical pure states of a d-level system has the form"

$$
\sqrt{F-\frac{1}{N+d}}=
\sqrt{(d-1)\left(\frac{N+1}{N+d}-G\right)}+
\sqrt{N\left(G-\frac{N}{N+d}\right)}.\tag{2}
$$

## Mathematical model

Section II, Eqs. (3)–(14), uses a Haar-uniform ensemble, N identical inputs and one output qudit. Covariance and Schur's lemma reduce optimization to a positive semidefinite seed on the symmetric input space tensor the output space, with trace D(N,d) = (N+d−1).choose(d−1). The scores are the real parts of trace(χ R_F) and trace(χ R_G). Equation (12) defines R_F by partial transposition of the full symmetric projector; Eq. (10) defines R_G by multiplication by the output reference projector, partial trace, and tensoring with the output identity.

The formal optimization ranges over every N ≥ 1 and d ≥ 2 and estimation scores in [N/(N+d−1), (N+1)/(N+d)]. It proves the squared form of Eq. (2), with attainment. The published reduction from arbitrary instruments and Haar integrals to seeds is an input to this model and is not separately formalized. The single-copy case is the fidelity balance of K. Banaszek, Physical Review Letters 86, 1366 (2001), cited as reference [7] in the source.

The occupation partition, uniform spectral bound, scalar optimization and attaining seeds are repository derivations. Literature completeness beyond the inspected citing works and Rapčan's thesis is ASSUMED-UNVERIFIED.
