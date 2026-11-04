---
bibkey: lucid2026structureddowndate
authors: Lucid (MathOverflow user 596445)
year: 2026
title: Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2
doi: null
url: https://mathoverflow.net/revisions/513954/2
claim: The source poses the complete structured-downdate inertia triple and continuous-family corollary and proposes the hyperplane decomposition and block congruences.
strata_touched:
  - D5/S3/QuadraticForms/StructuredRankOneInertia
  - D5/S3/QuadraticForms/StructuredRankOneFamily
license: CC-BY-SA-4.0
triage: anchor
---

## Verified locator

https://mathoverflow.net/revisions/513954/2

Revision 2, GUID 1084D752-1BBD-405E-B335-28FBDD1F4D6D. The version-specific source identifies Lucid, MathOverflow user 596445, and CC BY-SA 4.0.

## Mathematical scope

For real diagonal D and x with nonzero Delta=x-transpose D x, the source sets w=Dx and M=D-ww-transpose/Delta. It asks for the positive, negative and zero eigenvalue counts, with multiplicity, for both signs of Delta and with singular D allowed. The author proposes the hyperplane ker(w-transpose), its direct sum with span(x), and the resulting two block congruences. Sylvester's law supplies invariance under an invertible change of basis, without requiring invertibility of the form.

The related source corollary uses an open (n-1)-simplex with finitely many points removed, n at least three, continuous diagonal/vector families, nonzero Delta and positive semidefinite M. It asks for constant sign and, in the negative case, one globally fixed negative diagonal index. The inertia formula alone does not establish that entire source question.

The repository supplies the exact Lean definitions and completed derivations: real diagonal spectral counts, the symmetric-matrix kernel and nullity decomposition, both complete inertia triples, the explicit open-simplex log-ratio chart and finite-puncture transport, and the continuous-family global fixed-index argument and full conjunction. These are repository-derived results acknowledging the source questions and the author's proposed matrix mechanism; revision 2 does not attest these completed theorems. The augmented triangular congruences implement that proposed mechanism using standard Sylvester inertia. No ordinary novelty, priority, exhaustive literature search or global openness claim is made. Haynsworth's original paper is not a premise of the implementation.
