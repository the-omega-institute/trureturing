---
bibkey: doolittlechitambar2021certifying
authors: Brian Doolittle; Eric Chitambar
year: 2021
title: "Certifying the classical simulation cost of a quantum channel"
doi: 10.1103/PhysRevResearch.3.043073
url: https://arxiv.org/abs/2102.12543v1
claim: "A classical channel from n inputs to n' outputs is d-simulable when it is a shared-randomness mixture of encoders into d messages followed by decoders; these channels form the signaling polytope, and the signaling dimension is the least such d. The paper characterizes the signaling polytope for two-bit simulation of four-output channels, shows that six inputs suffice there to certify that one bit is not enough, and conjectures that binom(n', d) inputs always suffice to certify signaling dimension larger than d."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate
license: citation-only
triage: anchor
---

# Doolittle and Chitambar, Certifying the classical simulation cost of a quantum channel

B. Doolittle and E. Chitambar, arXiv:2102.12543v1 [quant-ph]; Physical Review Research 3(4), 043073 (2021). Quotations are from the v1 TeX source, with the source's macros `\mbf` and `\mc` (bold and calligraphic) expanded.

Equation (`Eq:d-simulate`), the channels simulable with $d$ messages:

> $$P(y|x)=\sum_\lambda q(\lambda)\sum_{m\in[d]}R_\lambda(y|m)T_\lambda(m|x),$$
> where $m\in[d]$ is the message sent from Alice to Bob and $T(m|x)$ (resp. $R(y|m)$) is an element of Alice's encoder $\mathbf{T}\in\mathcal{P}^{n\to d}$ (resp. Bob's decoder $\mathbf{R}\in\mathcal{P}^{d\to n'}$).

Definition `Def-signaling-polytope`:

> For given positive integers $n$, $n'$, and $d$, the set of all channels satisfying Eq. (`Eq:d-simulate`) constitute the *signaling polytope*, denoted by $\mathcal{C}_d^{n\to n'}$.

Theorem `Thm:main2`:

> For any integer $n$, a channel $\mathbf{P}\in \mathcal{P}^{n\to 4}$ belongs to $\mathcal{C}^{n\to 4}_2$ *iff* it satisfies the eight Bell inequalities depicted in Fig. (`Fig:6-2-4_facets`) and all their input/output permutations.

The conjecture, after that theorem:

> We conjecture that in general, no more than $\binom{n'}{d}$ inputs are needed to certify that a channel $\mathbf{P}\in\mathcal{P}^{n\to n'}$ has a signaling dimension larger than $d$.

## Verified locator

Source: https://arxiv.org/abs/2102.12543v1
- DOI: https://doi.org/10.1103/PhysRevResearch.3.043073 (Physical Review Research 3(4), 043073; published 26 October 2021; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2102.12543v1. The e-print is a gzipped tar archive; its member `main.tex` has 1963 lines and md5 `31f17f1218b2173973caccc946a33ddd`. Locations:
  - Eq. `Eq:d-simulate`, l. 153–156;
  - Definition `Def-signaling-polytope`, l. 158–162;
  - Definition `def-signaling-dimension`, l. 172–175;
  - Theorem `Thm:main2`, l. 402–405;
  - the conjecture, l. 409.
- The arXiv record lists one version (v1, 24 February 2021) and the journal reference "Phys. Rev. Research 3, 043073, 2021" (arXiv API metadata).
