---
bibkey: davaloszimanpineda2019divisibility
authors: David Davalos; Mario Ziman; Carlos Pineda
year: 2019
title: "Divisibility of qubit channels and dynamical maps"
doi: 10.22331/q-2019-05-20-144
url: https://arxiv.org/abs/1812.11437v4
claim: "A channel is divisible when it is a composition of two non-unitary channels; the P-divisible channels are those reached, up to closure, by continuous dynamical maps from the identity whose propagators are positive and trace preserving. For qubits every channel with negative determinant is entanglement breaking, so every divisible qubit channel outside the P-divisible set is entanglement breaking; the paper leaves open whether something similar holds in higher dimensions."
strata_touched:
  - D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation
license: citation-only
triage: anchor
---

# Davalos, Ziman and Pineda, Divisibility of qubit channels and dynamical maps

D. Davalos, M. Ziman and C. Pineda, arXiv:1812.11437v4 [quant-ph]; Quantum 3, 144 (2019). Quotations are from the v4 TeX source, with the source's macros `\mcE` (a calligraphic E), `{\sf C}^{\rm div}` and `\pDiv{}` (the sets $\mathsf C^{\rm div}$ and $\mathsf C^P$) expanded.

Divisible channels (Section 2.1):

> A quantum channel $\mathcal E$ is called *indivisible* if it cannot be written as a concatenation of two non-unitary channels, namely, if $\mathcal E = \mathcal E_1\mathcal E_2$ implies that either $\mathcal E_1$, or $\mathcal E_2$, exclusively, is a unitary channel. If the channel is not indivisible, it is said to be *divisible*.

Dynamical maps and P-divisibility (Section 2.2): a quantum dynamical map is a continuous curve $t\mapsto\mathcal E_t$ of channels on an interval with minimum $0$ and $\mathcal E_0=\mathrm{id}$; it is P-divisible if its propagators $\mathcal E_{t,s}$ are positive trace-preserving maps for all $t<s$; and

> we say $\mathcal E\in\mathsf C^P$ if there exists a P-divisible dynamical map $\mathcal E_t$ such that $\mathcal E=\mathcal E_t$ (with arbitrary precision) for some value of $t$ (including $t=\infty$).

Theorem 6 (Entanglement breaking channels and divisibility): for a qubit channel, $\det\hat{\mathcal E}<0$ implies that $\mathcal E$ is entanglement breaking, "i.e. all qubit channels outside" $\mathsf C^P$ "are entanglement breaking". The abstract ends:

> Finally, we show that every divisible but not infinitesimal divisible qubit channel (in positive maps) is entanglement breaking, and open the question if something similar occurs for higher dimensions.

## Verified locator

Source: https://arxiv.org/abs/1812.11437v4
- DOI: https://doi.org/10.22331/q-2019-05-20-144 (Quantum 3, 144; published 20 May 2019; title, authors, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/1812.11437v4. The e-print member `paper.tex` has 1634 lines and md5 `f16230f70c3fabbf4db44fae4c0c48f8`. Locations:
  - the abstract and its closing question, l. 149–167;
  - divisible channels, l. 255–262;
  - dynamical maps and P-divisibility, l. 281–295; the set $\mathsf C^P$, l. 336–339;
  - Theorem 6, l. 1237–1241.
- The arXiv record's latest version, v4, was posted on 19 January 2020 (arXiv API metadata).
