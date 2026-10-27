---
bibkey: tononilewenstein2025temporalbell
authors: Andrea Tononi; Maciej Lewenstein
year: 2025
title: "Temporal Bell inequalities in non-relativistic many-body physics"
doi: 10.1088/2058-9565/adcbce
url: https://arxiv.org/abs/2409.17290v4
claim: "The paper evaluates temporal Clauser-Horne correlators for the XX spin chain in a transverse field through the Jordan-Wigner fermions and their propagator, and conjectures a contraction identity Re[<0|f_N f_1 σ^x_N(t) f_1†|0> + <0|f_N f_1 σ^x_N(t) f_N†|0>] = Re[G_NN(t) - G_1N(t)], verified for 2 ≤ N ≤ 8 and assumed for every N."
strata_touched:
  - D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity
license: citation-only
triage: anchor
---

# Temporal Bell inequalities in non-relativistic many-body physics

A. Tononi and M. Lewenstein, arXiv:2409.17290v4 [quant-ph, cond-mat.quant-gas]; Quantum Sci. Technol. 10 (2025). Quotations are from the v4 TeX source.

The Jordan–Wigner Hamiltonian:

> $H = -J \sum_{i=1}^{N-1} \left( f_i^\dagger f_{i+1} + f_{i+1}^\dagger f_i \right) - \mu \sum_{i=1}^N f_i^\dagger f_i = \sum_{m=1, \atop k=k_m}^N \epsilon_k c_k^{\dag} c_k,$

The propagator:

> In particular, we find that $f_j^\dagger(t) = \sum_{i=1}^N G_{ij}(t) f_i^\dagger$, where we define the propagator $G_{ij}(t) = \sum_{m=1, \atop k=k_m}^N u_{ik} u_{jk} e^{i \epsilon_k t}$, with $u_{jk} = (-1)^{j-1} U_{j-1}(\lambda_k)/[\sum_{l=1}^{N} U_{l-1}^2(\lambda_k)]^{1/2}$ normalized eigenfunctions expressed in terms of the Chebyshev polynomials of second kind $U_{j-1}(\lambda_k) = \sin(j k)/\sin(k)$.

The Jordan–Wigner transformation (Methods):

> The inverse transformation is given by $\sigma^{+}_i = \prod_{j<i} (1 - 2 f^{\dag}_j f^{}_j ) f^{\dag}_i$ and $\sigma^{-}_i = \prod_{j<i} (1 - 2 f^{\dag}_j f^{}_j ) f^{}_i$.

The conjecture:

> However, we conjecture that $\text{Re}\big[ \bra{0} f_N f_1 \sigma^x_{N}(t) f_1^\dagger \ket{0} + \bra{0} f_N f_1 \sigma^x_{N}(t) f_N^\dagger \ket{0} \big] = \text{Re}\big[G_{NN}(t) - G_{1N}(t) \big]$, and we verified \cite{sneg} that the exact analytical form of the left- and right-hand sides coincides for $2\leq N \leq 5${, and with exact numerics} up to $N=8$ \cite{mullerrigat2025}. In the absence of a general proof, we assume the relation to hold for any value of $N$.

## Verified locator

Source: https://arxiv.org/abs/2409.17290v4
- URL: https://arxiv.org/abs/2409.17290v4 (source `arxiv.tex`, md5 `225051e786fe4712ac07f5226a0a99ac`):
  - the Hamiltonian, l. 144–150;
  - the propagator, l. 153–154;
  - the Jordan–Wigner transformation, l. 285–286;
  - the conjecture, l. 343–353.
- DOI: 10.1088/2058-9565/adcbce (https://doi.org/10.1088/2058-9565/adcbce; Crossref lists Quantum Science and Technology, volume 10, issued 17 April 2025).
