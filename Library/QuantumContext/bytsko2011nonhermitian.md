---
bibkey: bytsko2011nonhermitian
authors: A. G. Bytsko
year: 2011
title: "Non-Hermitian spin chains with inhomogeneous coupling"
doi: 10.1090/S1061-0022-2011-01148-3
url: https://arxiv.org/abs/0911.4476v3
claim: "The paper studies open U_q(sl_2)-invariant spin chains H = sum a_n P^{S,s}_{n,n+1} with |q| = 1, builds universal metric operators for them, determines the ranges of gamma with real spectra for short chains, and conjectures (Conjecture 3) that for |gamma| < pi/(2S) the spectrum is real whenever all couplings a_n are positive."
strata_touched:
  - D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation
license: citation-only
triage: anchor
---

# Non-Hermitian spin chains with inhomogeneous coupling

A. G. Bytsko, arXiv:0911.4476v3 (2010-02-10); Algebra i Analiz 22(3), 80–106 (2010); St. Petersburg Math. J. 22(3), 393–410 (2011). Quotations are from the v3 TeX source.

The coproduct:

> \Delta(E) = E \otimes K^{-1} + K \otimes E \,, \quad
> \Delta(F) = F \otimes K^{-1} + K \otimes F \,,
> \quad \Delta(K) = K \otimes K \,.

The representation:

> \pi_S(E)\,\omega_k &= \sqrt{[S{-}k][S{+}k{+}1]} \, \omega_{k+1} , \\
> \pi_S(F)\,\omega_k &= \sqrt{[S{+}k][S{-}k{+}1]} \, \omega_{k-1} ,

> \pi_S(K)\,\omega_k = q^k \, \omega_{k} ,

> where $[t] \equiv \frac{\sin \gamma t}{\sin \gamma}$.

The projectors:

> Let $\mathsf P^{S,s}$ denote the projector onto the irreducible
> submodule $V^s$ in $V^S \,{\otimes}\,V^S$.

The Hamiltonian:

> \mathsf H^{S,s}_{\{a_1,\ldots,a_{N-1}\}} =
>     \sum_{n=1}^{N-1} a_n \, \mathsf P^{S,s}_{n,n+1} \,,
>     \qquad  a_n \in \mathbb R \,,

The evidence and Conjecture 3:

> in the general $N \,{=}\,3$ case and the two--periodic
> $N \,{=}\,4$ case the spectra are always real if all
> coupling constants are positive. This observation
> is supported by numerical checks in a number of other cases.
> It is thus tempting to suggest the following.

> For $|\gamma| < \frac{\pi}{2S}$, the Hamiltonian (Hal)
> of a spin chain with inhomogeneous
> coupling has a real spectrum if all $a_n >0$.

The $N=4$ analysis is the subsection "$N=4$ and $N=5$ for $s=0$".

The tensor Casimir is introduced as $\mathcal C^{S,S}=(\pi_S\otimes\pi_S)\Delta(C)$ for the Casimir $C=\tfrac12(EF+FE)-\tfrac{\cos\gamma}{4\sin^2\gamma}(K-K^{-1})^2$ of Eq. (C). The expanded right-hand side printed in Eq. (dC2) does not commute with $\Delta(E)$; the definitional form does.

## Verified locator

Source: https://arxiv.org/abs/0911.4476v3
- URL: https://arxiv.org/abs/0911.4476v3 (source `main.tex`, md5 `dc29226c07d058043d2c18f82dbda3a4`):
  - the coproduct, l. 666–670;
  - the Casimir (C), l. 1531–1535;
  - the representation, l. 683–691;
  - the projectors, l. 776–777;
  - the Hamiltonian, l. 808–812;
  - the subsection on $N=4$ and $N=5$, l. 994;
  - the evidence and Conjecture 3, l. 1435–1446.
- DOI: 10.1090/S1061-0022-2011-01148-3 (https://doi.org/10.1090/S1061-0022-2011-01148-3).
