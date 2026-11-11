---
bibkey: vanherstraeten2024nongaussian
authors: Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf
year: 2024
title: "Classical capacity of quantum non-Gaussian attenuator and amplifier channels"
doi: 10.1142/S0219749924400033
url: https://arxiv.org/abs/2312.15623v2
claim: "The minimum output entropy of a phase-covariant attenuator channel ℳη,𝐩 is achieved by coherent states, ∀η,𝐩."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator
  - D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation
license: citation-only
triage: anchor
---

# Classical capacity of quantum non-Gaussian attenuator and amplifier channels

Z. Van Herstraeten, S. Guha and N. J. Cerf, Int. J. Quantum Inf. 22,
2440003 (2024), arXiv:2312.15623v2. Conjecture 2, section IV.B, PDF p. 12:

> The minimum output entropy of a phase-covariant attenuator channel
> $\mathcal{M}_{\eta,\mathbf{p}}$ is achieved by coherent states,
> $\forall\eta,\mathbf{p}$.

The domain is one bosonic mode, transmissivity $0\leq\eta\leq1$,
and every probability vector $\mathbf p$ on the nonnegative occupations.

The same section defines a phase-covariant attenuator by

$$
\mathcal{M}_{\eta,\mathbf{p}}[\hat\rho]
=\operatorname{Tr}_2\left[
\hat U_\eta\left(\hat\rho\otimes\sum_{n=0}^{\infty}p_n|n\rangle\langle n|\right)
\hat U_\eta^\dagger\right]
=\sum_{n=0}^{\infty}p_n\mathcal{M}_{\eta,n}[\hat\rho].
$$

The channel is a convex mixture of the Fock-environment attenuators.
The coherent state has coefficient
$e^{-|\alpha|^2/2}\alpha^n/\sqrt{n!}$ for every complex amplitude.
Beam-splitter displacement commutation implies that its output is a
displacement of the vacuum output, with retained amplitude
$\sqrt\eta\,\alpha$. The sign on the discarded-mode amplitude can be
changed by a second-mode phase convention; it does not affect the reduced
channel for a Fock-diagonal environment.

The formal result uses the mixed environment
$(7/8)|1\rangle\langle1|+(1/8)|5\rangle\langle5|$, the balanced beam
splitter, and the one-photon input. It refutes Conjecture 2. It does not
settle Conjecture 1 for pure Fock environments, nor assert that the
one-photon input is globally optimal. The paper states that geometric
probability vectors, corresponding to thermal environments, satisfy the
coherent-state minimum-output-entropy property by its cited Gaussian
optimizer result.

The full Hilbert space, global beam splitter, displacement covariance and
finite output entropy comparison are checked in Lean. The general
infinite-dimensional spectral characterization of the chosen entropy
definition is literature-attested in Wehrl's entropy review and is not
claimed here as a kernel-proved theorem.

## Locator

arXiv v2: https://arxiv.org/abs/2312.15623v2 — section IV.B, Conjecture 2,
PDF p. 12, and the mixed-environment channel definition.
Journal DOI: https://doi.org/10.1142/S0219749924400033.
The quoted statement and channel are read from the arXiv source; the journal
text has not been compared sentence by sentence.


## Prior balanced one-photon minimum

Zixuan He, *The energy cost of optical noise*, version 1.0,
DOI [10.5281/zenodo.23629201](https://doi.org/10.5281/zenodo.23629201),
publication date 25 October 2026, gives the balanced pure-one-photon
all-density spectral minimum and attainment by every coherent input.
This is a preprint; no journal acceptance is asserted.

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
