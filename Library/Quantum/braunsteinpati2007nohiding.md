---
bibkey: braunsteinpati2007nohiding
authors: Samuel L. Braunstein and Arun K. Pati
year: 2007
title: "Quantum Information Cannot Be Completely Hidden in Correlations: Implications for the Black-Hole Information Paradox"
doi: 10.1103/PhysRevLett.98.080502
claim: Exact input-independent quantum output requires the purifying subsystem to retain the input information; orthonormal purification vectors give the finite-dimensional replacement capacity bound.
strata_touched:
  - D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth
license: citation-only
triage: anchor
---

# No-Hiding and Universal Replacement

Braunstein and Pati's no-hiding theorem is the literature source for the
input-independent output condition and its purification-space consequence.
The repository represents the exact finite-dimensional condition as
`UniversalReplacement` and derives the orthonormal contraction family and
`dim B_next >= dim B_prev * rank tau` in
`universal_replacement_capacity_growth`.

The formal proof uses the repository's finite `DensityState` and
`partialTraceFirst`, then binds pinned Mathlib complex polarization, spectral
decomposition, and the dimension bound for linearly independent vectors.
It does not claim novelty, an approximate no-hiding result, a theorem about
small corrections, or a resolution of the black-hole information paradox.

## Search Log

- 2026-09-06: Crossref and the arXiv title query verified the authors, title,
  publication year, DOI, and `gr-qc/0603046` identifier.
- 2026-09-06: Read the arXiv PDF, section "Perfect hiding processes":
  equation (2) gives the spectral purification, equation (3) uses arbitrary
  complex superposition coefficients to annihilate cross terms, and the
  following paragraph constructs an orthonormal set spanning a Kd-dimensional
  ancilla subspace. These are the specific literature claims represented here.
- 2026-09-06: The initial guessed `quant-ph/0603046` identifier resolved to an
  unrelated paper and was discarded; it is not a source for this note.
- 2026-09-06: No complete replacement capacity theorem was found in current
  D5 or pinned Mathlib. The GitHub Lean search hit physlib channel APIs, but
  physlib is not an admitted dependency. The local proof follows rule 11(4)
  without changing the dependency pins.

## Verified locator

- https://doi.org/10.1103/PhysRevLett.98.080502
- https://arxiv.org/abs/gr-qc/0603046
