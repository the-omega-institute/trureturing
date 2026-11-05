---
bibkey: xieyounismeieberly2024journey
authors: Songbo Xie; Daniel Younis; Yuhan Mei; Joseph H. Eberly
year: 2024
title: "Multipartite Entanglement: A Journey Through Geometry"
doi: 10.3390/e26030217
url: https://arxiv.org/abs/2304.03281v2
claim: "The paper defines the four-qubit entropic fill from the volume of an entropic tetrahedron whose face areas are the one-to-other entanglement entropies, proves that it vanishes exactly on biseparable four-qubit pure states, states that the tetrahedron measure is a genuine four-qudit entanglement measure, and conjectures that it applies to qudit systems."
strata_touched:
  - D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation
license: citation-only
triage: anchor
---

# Multipartite Entanglement: A Journey Through Geometry

S. Xie, D. Younis, Y. Mei and J. H. Eberly, arXiv:2304.03281v2 [quant-ph]; Entropy 26(3), 217 (2024). Quotations are from the v2 TeX source.

The genuine requirement:

> The ``genuine'' requirement requires that a GME measure should only, and always, vanish for biseparable states \cite{ma2011,xie2021}.

The face equations, with $E_{i(jkl)}:=S(\rho_i)$ and $S(\rho)=-\text{Tr}(\rho\log_2\rho)$:

> \begin{equation}\label{eqn1}
> \sigma_{ij}+\sigma_{ik}+\sigma_{il}=E_{i(jkl)}.
> \end{equation}

The radical equations, with $E_{(ij)(kl)}:=S(\rho_{ij})$:

> \begin{equation}\label{eqn2}
> \begin{split}
> -\sqrt{\sigma_{ij}\sigma_{kl}}+\sqrt{\sigma_{ik}\sigma_{jl}}+\sqrt{\sigma_{il}\sigma_{jk}}=\lambda\cdot E_{(ij)(kl)}.
> \end{split}
> \end{equation}

The volume:

> \begin{equation}\label{volume}
> \begin{split}
> V&=\dfrac{\sqrt{2}}{3}S^{1/2}(A_0A_1A_2A_3)^{1/4},\\
> \text{with}\     A_0&=+\sqrt{\sigma_{12}\sigma_{34}}+\sqrt{\sigma_{13}\sigma_{24}}+\sqrt{\sigma_{14}\sigma_{23}},\\
> A_1&=-\sqrt{\sigma_{12}\sigma_{34}}+\sqrt{\sigma_{13}\sigma_{24}}+\sqrt{\sigma_{14}\sigma_{23}},\\
> A_2&=+\sqrt{\sigma_{12}\sigma_{34}}-\sqrt{\sigma_{13}\sigma_{24}}+\sqrt{\sigma_{14}\sigma_{23}},\\
> A_3&=+\sqrt{\sigma_{12}\sigma_{34}}+\sqrt{\sigma_{13}\sigma_{24}}-\sqrt{\sigma_{14}\sigma_{23}}.
> \end{split}
> \end{equation}
> and $S=2(\sigma_{12}+\sigma_{13}+\sigma_{14}+\sigma_{23}+\sigma_{24}+\sigma_{34})$, the total surface area of the entropic tetrahedron.

Scenario (c) of the proof of the genuine requirement:

> (c) $A_0=0$, but the assumption in (b) is not valid. It can be shown that the only possibility to maintain each square root being zero is $\sigma_{jk}=\sigma_{kl}=\sigma_{lj}=0$, while $\sigma_{ij}\neq0$, $\sigma_{ik}\neq0$, and $\sigma_{il}\neq0$. The four face areas satisfy the relations $E_{i(jkl)}=E_{j(kli)}+E_{k(lij)}+E_{l(ijk)}$ with $E_{i(jkl)}>E_{j(kli)}>0$, $E_{i(jkl)}>E_{k(lij)}>0$, and $E_{i(jkl)}>E_{l(ijk)}>0$, representing a tetrahedron with its four vertices coplanar. Using the same approach as in the appendix of \cite{xie2021}, a contradiction can be shown. Therefore, this scenario does not exist for four-qubit systems.\\

Scalability:

> Nonetheless, our tetrahedron measure presented in this work maintains its scalability. Specifically, we can consistently partition a large system into four groups and explore genuine quadripartite entanglement among these groups. Essentially, the tetrahedron measure is a genuine four-qudit entanglement measure, where each party possesses more than two dimensions. The extension of entropic fill to qudit systems has been made possible by a recent study \cite{yang2022}. Additionally, we have conducted numerical verifications, demonstrating the existence of unique nonnegative solutions for Eq.~\eqref{eqn1} and \eqref{eqn2} in qudit systems up to $d=50$. Consequently, we conjecture that our tetrahedron measure is also applicable to qudit systems.

## Verified locator

Source: https://arxiv.org/abs/2304.03281v2
- URL: https://arxiv.org/abs/2304.03281v2 (source `tetrahedron.tex`, md5 `da0b24bf21c330f90979f63e7679749c`):
  - the genuine requirement, l. 57;
  - the entropies, l. 65 and l. 107;
  - the volume, l. 92–101;
  - the face equations, l. 104–106;
  - the radical equations, l. 117–121;
  - the entropic fill, l. 128;
  - scenario (c), l. 135;
  - Scalability, l. 220.
- DOI: 10.3390/e26030217 (https://doi.org/10.3390/e26030217).
