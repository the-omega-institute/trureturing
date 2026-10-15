---
bibkey: idealintersection2026sixsupport
authors: the-omega-institute/ideal-intersection-laplacian contributors
year: 2026
title: "Six-support complement quotient and uniform low root"
doi: null
url: https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex
claim: "The public source gives the six-support quotient, weighted energy, uniform positive-real low-root theorem, and balanced sharpness formula."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot
license: citation-only
triage: anchor
---

# Six-support quotient source

## Verified locator

URL: https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex

The pinned file has 52,245 bytes and SHA256
`8553e367c53f71840404e13967395791748a57f1ced4bacf105f36e5fcb477c8`.
The matrix and zero-kernel relations occur on lines 574–600; the
weighted-energy argument on lines 774–784; the symmetric block and
Schur complement on lines 850–913; the uniform-low-root theorem on
lines 915–972; and balanced sharpness on lines 114–145.

The mathematical model and stated results belong to this public source.
The Lean proofs and the exposition in the corresponding Blueprint are
independently authored. The source is cited, not reproduced or treated
as a source-code license. Generic spectral and matrix results are reused
from the pinned Mathlib and repository libraries. No discovery or
priority claim follows from this formalization.

The explicit two-dimensional comparison plane
`(x, sqrt(b)y, sqrt(c)y)` and its completed-square identity are a
repository synthesis of the source's comparison geometry. They replace
its determinant-to-inertia step on the live proof path. The transition
construction likewise completes a square in the positive singleton
coordinate after eliminating the two positive paired diagonals. These
constructions preserve the real domain and the singular boundary
`a = 3`. The generic spectral expansion is supplied by `RHLinalg` and
Mathlib; it is not claimed as new mathematics.
