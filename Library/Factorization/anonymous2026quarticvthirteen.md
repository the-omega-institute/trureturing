---
bibkey: anonymous2026quarticvthirteen
authors: Unattributed manuscript in the elliotglazer repository
year: 2026
title: Z is Diophantine in Q, Version 13
doi: null
url: https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/manuscripts/quartic_v13.tex
claim: The generator proposition uses local cancellation bounds six at sqrt(2), four at 3-sqrt(2), and no other prime support for the primitive duplication forms.
strata_touched:
  - D5/S3/Factorization/QuadraticIdeals/SqrtTwoDuplicationCancellation
license: No redistribution grant established; mathematical statement cited, no source code transplanted
triage: anchor
---

# Primitive duplication cancellation

## Verified locator

https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/manuscripts/quartic_v13.tex

The duplication forms and the local arithmetic occur at lines 370–385 in the proof
of `prop:generator`. The following displayed inequalities use the normalized
absolute projective logarithmic height and the constants 392 and 676.
The manuscript credits the generator argument to Proposition 2.1 of the
OpenAI preprint cited there. This is attribution of a known mathematical argument,
without a claim of discovery or a verified priority chain.

The Lean proof is independently authored over the pinned Mathlib quadratic order.
It proves the two ideal-power noncontainments and the complete prime support.
Identifying the explicit order with the number field's full ring of integers,
converting to an ideal norm, and obtaining the all-point normalized height bound
are separate mathematical obligations.

The source does not identify an author in its author field. Public source
availability does not establish permission to transplant upstream Lean code.
