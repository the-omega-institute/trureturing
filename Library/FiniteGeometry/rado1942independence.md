---
bibkey: rado1942independence
authors: Richard Rado
year: 1942
title: A theorem on independence relations
doi: 10.1093/qmath/os-13.1.83
url: https://doi.org/10.1093/qmath/os-13.1.83
claim: Independent representatives exist when every subfamily has rank at least its cardinality.
strata_touched:
  - D5/S3/Combinatorics/Matroids/LinearRado
  - D5/S3/Combinatorics/Matroids/Rado
license: citation-only
triage: anchor
---

# Rado, independent representatives

## Verified locator

DOI: 10.1093/qmath/os-13.1.83

Source: https://doi.org/10.1093/qmath/os-13.1.83

Rado's independent representative theorem specializes to vector subspaces: representatives can be chosen linearly independently exactly when the span of every subfamily has dimension at least its cardinality. The spanning version follows by adjoining a common auxiliary vector space of the required deficit dimension, choosing independent representatives, and projecting back.

This is the classical linear representative theorem. It is distinct from the q-analogue of Rado's theorem posed as Conjecture 1 in Saaltink's paper.

The native finite-matroid criterion is
`D5.S3.Combinatorics.Matroids.Rado.rado_independent_transversal`.
Its index and carrier types lie in independent universes and are only assumed finite.
The matroid ground and the representative sets are arbitrary; the empty cases are included.

The Lean source is adapted from
[facebookresearch/atlas-lean, MathlibExt/Combinatorics/Matroid/Rado.lean](https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Combinatorics/Matroid/Rado.lean),
revision `a60759060b5616df0d5775b42da4d337719feb32`,
blob `4524c838af21f3e5174a5ca2d71b2d6f70bfdab9`,
SHA256 `b057068d0e91843062b9069c997e49236e952e07368edb2bf578c60a9e6b3f34`.
The original Meta copyright notice is retained in the source; the full supplier
[license](../../docs/reports/lovasz-suppliers/atlas-LICENSE.txt), including its intended-use
preface, applies to the source port. The adaptations use the native contraction-rank
identity, preserve the finite-family induction, rename the endpoint and namespace,
make the independent universes explicit, and omit the unused full-ground wrapper.
Direct upstream reuse replaces this port when the actual pinned Mathlib contains an
equivalent full-scope criterion with accepted standard axiom closure.
