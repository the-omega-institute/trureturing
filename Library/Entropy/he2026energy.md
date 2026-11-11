---
bibkey: he2026energy
authors: Zixuan He
year: 2026
title: "The energy cost of optical noise"
doi: 10.5281/zenodo.23629201
claim: "For the balanced pure-one-photon attenuator, every normal input state has output spectral entropy at least log 2, and vacuum and every coherent input attain this minimum."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedSpectralEntropy
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment
license: citation-only
triage: anchor
---

# Balanced one-photon minimum and coherent attainment

Version 1.0 is a preprint; no journal acceptance is asserted.

Section 2 defines normal states as arbitrary positive trace-class
trace-one operators and allows infinite entropy. Equation (8) at
`j = 2` and `eta = 1/2` gives the pure one-photon environment.
Theorem 2 (PDF page 5) gives spectrum `(1/2, 1/2)`, the all-input
majorization bound, and minimum spectral entropy `log 2`, attained by
every coherent input. Appendix A.2-A.3 (PDF pages 18-19) treats the
completed optical isometry, actual attenuator identity (67), and
operator cap (69), including mixed normal states and arbitrary tails.

The corresponding native formalization is in `BalancedHalfCap`,
`BalancedSpectralEntropy`, and `BalancedAttainment` under
`D5/S3/Quantum/QuantumChannels/FockAttenuator`. It retains all density
inputs and the native extended spectral entropy. Its all-odd-occupation
balanced cap and entropy floor assert no attainment for odd occupations
greater than one and no priority for that application. It does not
claim a new literature resolution, other transmissivities, a full
Conjecture 1 resolution, or equality with the separate basis-infimum
entropy API. The preprint's broader claims are outside this
formalization's scope.

## Locator

DOI: https://doi.org/10.5281/zenodo.23629201 — version 1.0,
Theorem 2 (PDF page 5) and Appendix A.2-A.3 (PDF pages 18-19).
The primary PDF has SHA-256
`da209777d7d0b8144a3cb6d31ad05b1a5d3baef4609f9519aacf606147875fb0`.

The four exact one-photon entropy/attainment/minimality conclusions in
`BalancedAttainment` and the one-photon lower bound in
`BalancedSpectralEntropy` are literature-attested by this result.
The density/pure-channel bridge, general spectral helpers and odd-family
derivations retain their repository-derived classification. That
classification does not claim literature novelty or priority.
