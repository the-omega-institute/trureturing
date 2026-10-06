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
