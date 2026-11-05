---
bibkey: atlas2026douglas
authors: Meta Platforms, Inc. and affiliates
year: 2026
title: Douglas lemma for bounded operators on Hilbert spaces
doi: null
url: https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean
claim: Actual range inclusion, bounded factorization and pointwise adjoint norm majorization are equivalent for bounded maps between arbitrary complete RCLike inner product spaces; every given nonnegative majorization constant bounds a realizing factor.
strata_touched:
  - D5/S3/HilbertOperators/DouglasLemma
license: upstream LICENSE including intended-use preface; see docs/reports/lovasz-suppliers/atlas-LICENSE.txt
triage: anchor
---

# Douglas factorization for Hilbert spaces

The Lean supplier is the selected source file of facebookresearch/atlas-lean,
revision `a60759060b5616df0d5775b42da4d337719feb32`. Its copyright holder is
Meta Platforms, Inc. and affiliates; the file has no separate author line.
The bibliographic year identifies this source release, rather than the
original classical theorem.

For any RCLike field k and complete inner product spaces E and F, with
three independent universes, bounded maps A and B from E to F satisfy:
actual Range(A) is included in actual Range(B) if and only if A = B composed
with some bounded endomorphism C of E, and if and only if some nonnegative
real c bounds norm(Adjoint(A)y) by c times norm(Adjoint(B)y) for every y in F.
For each given c satisfying that bound, a single C realizes the factorization
and has operator norm at most c. The spaces may be zero-dimensional,
infinite-dimensional or nonseparable; ranges need not be closed and maps
need not be injective or surjective.

Range inclusion gives a canonical orthogonal preimage in the complement of
Kernel(B). Its linearity follows from uniqueness and its continuity from the
closed graph theorem. Majorization gives a bounded extension from the range
of Adjoint(B) to its closure S. Taking the adjoint of that extension composed
with the orthogonal projection onto S gives the factor and the prescribed
norm bound. S is an internal extension domain: the range-inclusion conclusion
uses actual ranges. No optimal-constant attainment formula, distinct source
domains, Hilbert C*-module extension, numerical algorithm or empirical
quantum conclusion is asserted.

## Source correspondence and license

The original source SHA-256 is
`da771a6432fc65f0f608e74a13a17c6e3a39b275563e436105743ce8ccf191db`.
The retained source is `D5/S3/HilbertOperators/DouglasLemma.lean`.
Its narrow packaging adds the canonical D5 header and namespace, removes
upstream module/public wrappers, and omits only the unconsumed APIs
`douglasFactor_mem_orthogonal` and
`douglasFactor_eq_of_mem_orthogonal_and_apply`. Every retained relative
declaration name, mathematical statement and proof body is preserved.
This is reuse of known mathematics and a formal source transplant, with
no reproof or novelty claim.

The upstream copyright and license notice reads:

```text
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
```

The full root LICENSE is already retained in
`docs/reports/lovasz-suppliers/atlas-LICENSE.txt`, including its intended-use
preface concerning machine learning. Its length is 11,463 bytes and SHA-256 is
`fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.
This reference covers the selected source; it does not assert blanket legal
clearance. The complete upstream Git tree has 22,538 entries, is not
truncated, and contains no NOTICE file, as verified by the source-intake
caller.

The source and this repository use Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Equal pins do not themselves
establish package admission. No dependency on the atlas project is added.
Retire this transplant and directly reuse Mathlib when this repository
actually adopts a Mathlib revision supplying equivalent complete actual-range,
factorization, majorization and every-given-constant norm-bound statements
on arbitrary complete RCLike inner product spaces.

## Classical literature and scope

R. G. Douglas, *On majorization, factorization, and range inclusion of operators
on Hilbert space* (1966), DOI `10.1090/S0002-9939-1966-0203464-1`, is the
classical reference. Only its Crossref metadata has been read; the original
AMS article body has not been inspected. No original-paper theorem locator
is claimed.

The readable expositions by V. M. Manuilov, M. S. Moslehian and Q. Xu,
*Douglas factorization theorem revisited*, arXiv:1807.00579v3,
https://arxiv.org/abs/1807.00579v3, and S. Nayak,
*The Douglas lemma for von Neumann algebras and some applications*,
arXiv:1707.04378v2, https://arxiv.org/abs/1707.04378v2,
Theorem 1.1, supply classical same-space formulations. Their relevant
statements have been read. The precise arbitrary two-space, RCLike and
independent-universe scope here is supplied by the immutable Lean source,
not attributed to an unread original paper or inferred from these expositions.

## Verified locator

https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean
contains `range_le_iff_exists_factorization`,
`majorization_iff_exists_factorization`, `range_le_iff_majorization` and
`exists_factorization_of_majorization`, with the canonical-factor
construction and its support declarations. The complete license is
https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/LICENSE.
The classical DOI is https://doi.org/10.1090/S0002-9939-1966-0203464-1;
it identifies the original article bibliographically and does not replace
the exact Lean supplier above.
