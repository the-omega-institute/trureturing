---
bibkey: chitambar2014locc
authors: Eric Chitambar, Debbie Leung, Laura Mančinska, Maris Ozols, Andreas Winter
year: 2014
title: "Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask)"
doi: 10.1007/s00220-014-1953-9
url: https://arxiv.org/abs/1210.4583
claim: "Section 2.2 defines finite-round LOCC_r, their union LOCC_ℕ, and LOCC including unbounded-round protocols, and establishes LOCC_ℕ ⊆ LOCC ⊆ cl(LOCC_ℕ)."
strata_touched:
  - D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1007/s00220-014-1953-9

Source: https://arxiv.org/abs/1210.4583

Crossref resolves this DOI to the stated title and authors, published in
Communications in Mathematical Physics 328, 303–326.

Section 2.1, pp. 4–5 of the arXiv text, defines convergence of instruments
using the diamond norm. For a fixed finite outcome set, this is the usual
finite-dimensional topology.

Section 2.2, p. 5, defines LOCC_r recursively by one-way local instruments
and conditional composition, LOCC_ℕ as their union over finite r, and LOCC
by a linked sequence of finite-round instruments whose coarse-grainings
converge to the target instrument. Section 2.2, p. 6, states the inclusion
$\mathrm{LOCC}_{\mathbb N}\subseteq\mathrm{LOCC}\subseteq
\overline{\mathrm{LOCC}_{\mathbb N}}$ and identifies the common closure.
LOCC includes both bounded-round and unbounded-round protocols.

## Application to discrimination

For a finite ensemble and a fixed finite set of reported labels, success is
a continuous linear functional of the measurement effects. Consequently
its supremum over LOCC_ℕ, LOCC and the closure of LOCC_ℕ is the same.
This application is an argument on paper. The settling Lean module uses
finite trees of complete square local Kraus instruments; output spaces can
be pulled back by polar decomposition, preserving the measurement statistics.
Neither this correspondence nor the equality of suprema is a Lean theorem
in that module.
