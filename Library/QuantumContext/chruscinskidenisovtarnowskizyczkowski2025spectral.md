---
bibkey: chruscinskidenisovtarnowskizyczkowski2025spectral
authors: Dariusz Chruściński; Sergey Denisov; Wojciech Tarnowski; Karol Życzkowski
year: 2025
title: "Spectral delineation of Markov generators: classical vs quantum"
doi: 10.1088/1751-8121/ae58d2
url: https://arxiv.org/abs/2504.07903v1
claim: "The paper rescales generators of classical and quantum Markov semigroups so that their spectra lie in the disk of radius one centred at -1, proves such confinement for purely dissipative GKLS generators under a quantum rescaling parameter, and conjectures (Conjecture 3) that for generators of positive trace-preserving dynamics the scale given by the maximal absolute diagonal value on pure states already confines the spectrum."
strata_touched:
  - D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation
license: citation-only
triage: anchor
---

# Spectral delineation of Markov generators: classical vs quantum

D. Chruściński, S. Denisov, W. Tarnowski and K. Życzkowski, arXiv:2504.07903v1 (2025); published in J. Phys. A 59 (2026) as "Corralling spectra of generators of time-continuous Markov evolution (both classical and quantum)". Quotations are from the v1 TeX source.

The GKLS form:

> $\mathcal{L}(\rho) = -i[H,\rho] + \sum_k \gamma_k \Big( L_k \rho L_k^\dagger - \frac 12 \{ L_k^\dagger L_k, \rho\} \Big),$

> where $H$ is an Hermitian operator (effective system's Hamiltonian), $L_k$ are the so-called jump operators, and $\gamma_k > 0$ are the damping rates.

The canonical form of a purely dissipative generator:

> $\mathcal{L}(\rho) = \sum_\alpha \gamma_\alpha \left( L_\alpha \rho L_\alpha^\dagger - \frac 12 \{  L_\alpha^\dagger L_\alpha,\rho\} \right)$

> with ${\rm Tr}L_\alpha =0$, and ${\rm Tr}  (L_\alpha^\dagger L_\beta) =\delta_{\alpha\beta}$.

Conjecture 3:

> If $\mathcal{L}$ is a generator of positive trace-preserving dynamics and $\nu_{\text{q},3} := \max_{\|\psi\|=1} | \langle \psi|\mathcal{L}(|\psi\rangle\langle\psi|)|\psi\rangle|$, then the spectrum of $\frac{1}{ \nu_{\text{q},3}}  \mathcal{L}$ is confined in the unit disk $\mathbb{D}(-1,1)$.

## Verified locator

Source: https://arxiv.org/abs/2504.07903v1
- URL: https://arxiv.org/abs/2504.07903v1 (source `bounding_6.tex`, md5 `31cb6e7a93cfb4dac99f83105a784d57`):
  - the GKLS form, l. 205–209;
  - purely dissipative generators and the disk $\mathbb{D}(-1,1)$, l. 224–227;
  - the canonical traceless form, l. 794–799;
  - Conjecture 3, l. 1044–1050.
- DOI: 10.1088/1751-8121/ae58d2 (https://doi.org/10.1088/1751-8121/ae58d2).
