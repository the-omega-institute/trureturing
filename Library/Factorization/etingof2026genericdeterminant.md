---
bibkey: etingof2026genericdeterminant
authors: mathlib-initiative
year: 2026
title: Auxiliary matrix determinant irreducibility, clean Lean release
doi: null
url: https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1/blob/c6d86a8bd52065aafb8251fa1cdcd55b609743ef/clean-code/release/RepresentationTheory/AuxiliaryMatrixDeterminantIrreducibility.lean
claim: The determinant of the full positive-size complex generic matrix is irreducible.
strata_touched:
  - D5/S3/Quantum/Algebra/GenericMatrixIrreducibility
license: Apache-2.0
triage: anchor
---

# Full generic determinant

## Verified locator

https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1/blob/c6d86a8bd52065aafb8251fa1cdcd55b609743ef/clean-code/release/RepresentationTheory/AuxiliaryMatrixDeterminantIrreducibility.lean

The exact clean release has Git blob df299f60e7f2bbf2c02aab007fb3a957d2a91510
and SHA-256 1959a1acc6fe09934add2c8adc4ab7178b947f20fa71f61488e6463f930daf74.
Its 318 lines and 13,368 bytes contain the public theorem
`RepresentationTheory.AuxiliaryMatrixDeterminantIrreducibility.det_auxiliaryMatrix_irreducible_of_pos`.
The private `genMatrix` is definitionally `Matrix.mvPolynomialX`.

## Source mapping

The determinant portion of `D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.lean`
faithfully transplants the proof, with the original copyright header. The full
release license and unchanged NOTICE are respectively
`docs/reports/generic-matrix-suppliers/Etingof-LICENSE.txt` and
`docs/reports/generic-matrix-suppliers/Etingof-NOTICE.txt`.
The namespace and public name are adapted, the public statement uses
`Matrix.mvPolynomialX` directly, the unused reflexive private equality is omitted,
and the project-specific `source_ref` attribute is omitted. Narrow Mathlib imports
replace the upstream umbrella and alignment imports. The determinant proof itself
is retained. The characteristic-polynomial bridge is local code implementing the
closed argument cited in the companion Brešar–Špenko note. No novelty is claimed.

## Pin compatibility and retirement

The release pins Lean v4.32.2 and Mathlib
905b95818eb32af7874a58b427f50c1711a5e96c. This repository pins Lean v4.35.0 and
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, so a package dependency cannot
share this repository's resolution. This is the transplantation form of SPEC A17.2.
Retire this determinant transplant when this repository's own pinned Mathlib
contains an equivalent theorem for every positive size over the full complex
coefficient polynomial ring. Check that declaration's telescope and compile its
exact application; then replace live consumers by direct applications and remove
the transplanted proof. Acceptance elsewhere alone does not trigger retirement.
