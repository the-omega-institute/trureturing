---
bibkey: kimmel2015robustphase
authors: Shelby Kimmel; Guang Hao Low; Theodore J. Yoder
year: 2015
title: Robust Calibration of a Universal Single-Qubit Gate-Set via Robust Phase Estimation
doi: 10.1103/PhysRevA.92.062315
url: https://arxiv.org/abs/1502.02677v3
claim: Robust multiscale phase estimation calibrates single-qubit gates; the 2021 erratum corrects the branch-error threshold used in the original analysis.
strata_touched:
  - D5/S3/ObserverMemory/Trajectories/FibonacciNearReturn
license: citation-only
triage: anchor
---

# Multiscale phase estimation and the corrected angle margin

The arXiv v3 record dated 2021-10-21, the parsed Section V and the first-page erratum were read. The erratum page was rendered and inspected. The published correction is Physical Review A 104, 069901 (2021), DOI 10.1103/PhysRevA.104.069901. The original error analysis used an insufficient pi/2 condition; the corrected branch argument requires the pi/3 margin discussed in the erratum. The paper states that the overall robust calibration approach remains valid with modified constants.

The proposed Section 19 continuation of the unified predictive-geometry volume reuses geometric-time unwrapping, proves its scalar branch condition directly with 3a < pi, and specifies independent real/imaginary Gaussian readings. That Gaussian experiment differs from the paper's quantum preparation, gate and measurement-error model. Its resource counts and probabilities are derived independently.

The candidate matrix result is a finite-horizon Hilbert-Schmidt intertwining certificate from a dyadic set of times. This note does not attribute that result to the paper, claim it is absent from all prior literature, or certify it through the existing Fibonacci Lean declaration. The multiscale decoding idea itself is prior art. The complete Section 19 proof is delivered in the original PR discussion and patch until the main-volume file is actually updated.
