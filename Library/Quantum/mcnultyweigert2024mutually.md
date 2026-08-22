---
bibkey: mcnultyweigert2024mutually
authors: Daniel McNulty, Stefan Weigert
year: 2024
title: Mutually Unbiased Bases in Composite Dimensions -- A Review
doi: 10.48550/arXiv.2410.23997
claim: The review records the open existence problem for four mutually unbiased bases in dimension six and presents fourteen mathematically equivalent formulations of the existence problem.
strata_touched:
  - D5/S3/Quantum/Tomography/RankOneContextCommutator
  - D5/S3/Quantum/Tomography/CompleteContextTomography
  - D5/S3/Quantum/Tomography/ComplementaryContextProbabilityPythagoras
  - D5/S3/QuantumBounds/Designs/CollisionConservation
license: citation-only
triage: anchor
---

# Mutually Unbiased Bases in Composite Dimensions -- A Review

McNulty and Weigert review the construction and nonexistence questions for
mutually unbiased bases in composite dimensions. For dimension six they keep
two conjectures separate. Conjecture 1.1 concerns a complete family, which
would contain seven bases, while Conjecture 2.1 is Zauner's `k = 4` affine
quantum-design formulation of the fourth-basis problem. The latter is the
source anchor for `Problems/mub-six-fourth-basis.md`.

The review's abstract also reports fourteen mathematically equivalent
formulations of the existence problem. This note does not transfer those
equivalences into the repository and does not treat any numerical obstruction
as a proof of nonexistence.

## Search log

- 2026-08-22: The orchestrator queried the arXiv Atom API with
  `id_list=2410.23997`. HTTP 200 returned one entry whose title and authors
  matched this note. The entry was published 2024-10-31, updated 2026-03-26,
  and assigned primary category `quant-ph`; it also reported journal DOI
  `10.22331/q-2026-04-01-2051`. The same probe returned one entry for positive
  control `2002.03233` and zero entries for negative control `9999.99999`.
- 2026-08-22: The orchestrator issued
  `HEAD https://doi.org/10.48550/arXiv.2410.23997`. It returned HTTP 302 to
  `https://arxiv.org/abs/2410.23997`; negative control
  `10.48550/arXiv.9999.99999` returned HTTP 404.
- 2026-08-22: The orchestrator read the arXiv HTML for version 2 and located
  Conjecture 1.1 and Conjecture 2.1, with `k = 4` in the latter. A proposed
  alternative numbered locator was absent, so only these verified conjecture
  labels are used.
- 2026-08-22: The orchestrator's full-tree fixed-string search found zero D5
  hits for `MutuallyUnbiased`, `mutually_unbiased`,
  `MutuallyUnbiasedBases`, `ComplexHadamard`, `complexHadamard`, and
  `HadamardMatrix`; `RankOneContext` supplied the positive control. The
  implementation worker reproduced these zero counts and the positive-control
  hit in the current checkout.

## Verified locator

- arXiv: https://arxiv.org/abs/2410.23997
- arXiv DOI: https://doi.org/10.48550/arXiv.2410.23997
- arXiv HTML v2: https://arxiv.org/html/2410.23997v2
- Journal DOI, not the canonical DOI of this note:
  https://doi.org/10.22331/q-2026-04-01-2051
