---
bibkey: cleve1999share
authors: Richard Cleve, Daniel Gottesman, and Hoi-Kwong Lo
year: 1999
title: How to share a quantum secret
doi: 10.1103/PhysRevLett.83.648
claim: The three-qutrit ((2,3)) threshold encoding has maximally mixed single shares and permits exact recovery from any two shares.
strata_touched:
  - D5/S3/Quantum/Entanglement/QutritThresholdSharing
license: citation-only
triage: anchor
---

# How to share a quantum secret

The cited paper supplies the quantum threshold-sharing construction. The
formalized instance uses computational-basis labels in ZMod 3 and the
encoding V|s> = (1/sqrt(3)) sum_j |j,j+s,j+2s>. Every single-share marginal
is I_3/3. The two-share decoder sends |a,b> to |b-a,2b-a>, with inverse
|u,v> to |v-2u,v-u>. It recovers the input and leaves the fixed entangled
state (1/sqrt(3)) sum_r |r,r> in the remaining output factors.

The module uses complex amplitude functions and finite matrices. Its cyclic
coordinate helper and partial-trace adapter express the same construction
for the ordered pairs (1,2), (2,3), and (3,1); they are representation choices,
not additional claims of mathematical novelty. The matrix-unit computation
is exposed separately and extended to the repository's canonical density
states. No general ((k,n)) existence theorem, entropy table, or black-hole
dynamics is claimed.

## Search Record

- 2026-09-06: Read the authoritative ingested single-share and two-share
  statements and their shared encoding definition in the source volume.
- 2026-09-06: Retrieved https://arxiv.org/abs/quant-ph/9901025, which confirms
  the authors, title, submission year, journal reference, and DOI above.
- 2026-09-06: Searched current repository declarations, pinned Mathlib, the
  supplied in-flight inventory, and indexed GitHub Lean code for qutrit and
  quantum secret-sharing statements. No covering declaration was identified
  in those searched scopes; the detailed queries are in the seat report.

## Verified locator

- arXiv abstract and bibliographic record: https://arxiv.org/abs/quant-ph/9901025
- DOI: https://doi.org/10.1103/PhysRevLett.83.648
- Journal reference recorded by arXiv: Physical Review Letters 83, 648-651 (1999).
