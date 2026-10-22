---
bibkey: chitambargeorgedoolittlejunge2023communication
authors: Eric Chitambar; Ian George; Brian Doolittle; Marius Junge
year: 2023
title: "The Communication Value of a Quantum Channel"
doi: 10.1109/TIT.2022.3218540
url: https://arxiv.org/abs/2109.11144v1
claim: "The paper defines the communication value cv of a quantum channel as the largest unnormalized guessing score of the classical channels it induces, its entanglement-assisted version cv*, characterizes both by conic programs over the separable and positive cones, and conjectures cv*(N) <= d_B cv(N) for every channel."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue
license: citation-only
triage: anchor
---

# The Communication Value of a Quantum Channel

E. Chitambar, I. George, B. Doolittle and M. Junge, arXiv:2109.11144v1 (2021-09-23); IEEE Trans. Inf. Theory 69(3), 1660–1679 (2023). Quotations are from the v1 TeX source.

The communication value of a classical channel (`Eq:Cv`):

> \cv(\mbf{P})=\sum_{y\in[n']}\max_{x\in[n]}P(y|x).

The communication value of a quantum channel (`Defn:cv`):

> The $[n]\to[n']$ communication value (cv) of a quantum channel $\mc{N}\in\cptp(A\to B)$ is
> \cv^{n\to n'}(\mc{N})=\max_{\substack{\{\Pi_{y}\}_{y=1}^{n'}\\\{\rho_x\}_{x=1}^n}}\{\cv(\mbf{P})\;|\; P(y|x)=\tr[\Pi_y\mc{N}(\rho_x)]\},
> and the cv value of $\mc{N}$ is defined as
> \cv(\mc{N})=\sup_{n,n\in\mbb{N}}\cv^{n\to n'}(\mc{N}).

The entanglement-assisted protocol (`Eq:Ea-cv`):

> P(y|x)=\tr\left[\Pi_y^{BB'}\left(\mc{N}^{A\to B}\circ\mc{E}_x^{A'\to A}\otimes\id^{B'}[\varphi^{A'B'}]\right)\right].

The entanglement-assisted communication value:

> The entanglement-assisted communication value (ea cv) of a quantum channel $\mc{N}\in\cptp(A\to B)$, denoted $\cv^{*}(\mN)$, is
> \sup_{\varphi^{A'B'}}\max\{\cv(\mbf{P})\;|\;\text{$P(y|x)$ given by Eq. \eqref{Eq:Ea-cv}}\} \, ,
> where the supremum is taken over all entangled states $\varphi^{A'B'}$ (and all dimensions $A'B'$), while the maximization considers all $n,n'\in\mbb{N}$ along with arbitrary states $\{\rho_x\}_{x\in[n]}$ and POVMs $\{\Pi_y\}_{y\in[n']}$.

The conjecture:

> \noindent\textit{Conjecture}:  For any channel $\mc{N}\in\cptp(A\to B)$,
> \cv^*(\mc{N})\leq d_B\cdot \cv(\mc{N}).

## Verified locator

Source: https://arxiv.org/abs/2109.11144v1
- URL: https://arxiv.org/abs/2109.11144v1 (source `arxiv_draft_v1.tex`, md5 `7008e4461225de9fc07e55cf4b3ffcce`):
  - the classical communication value, l. 128–131;
  - the communication value of a quantum channel, l. 143–153;
  - the entanglement-assisted protocol, l. 1353–1356;
  - the entanglement-assisted communication value, l. 1358–1364;
  - the conjecture, l. 1462–1465.
- DOI: 10.1109/TIT.2022.3218540 (https://doi.org/10.1109/TIT.2022.3218540).
