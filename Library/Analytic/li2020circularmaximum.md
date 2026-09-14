---
bibkey: li2020circularmaximum
authors: Hui Li, Jun Wang, Xiao Yao, Zhuan Ye
year: 2020
title: Inequalities Concerning Maximum Modulus and Zeros of Random Entire Functions
doi: null
url: https://arxiv.org/abs/2012.07453
claim: Standard circular maximum-modulus notation is represented by a real supremum, with attainment for continuous functions supplied by the compact extreme value theorem.
strata_touched:
  - D5/S3/Analytic/Entire/SquareShadowOrderHalving
license: citation-only
triage: anchor
---

# Circular suprema and compact attainment

## Verified locator

The exact upstream locator is:
https://arxiv.org/abs/2012.07453

The arXiv record and PDF were retrieved. Section 2 explicitly writes
`M(r,f_omega) = max_{|z|=r} |f_omega(z)|` in its notation for random entire
functions. This supplies the standard notation. The theorem carrying the
attainment claim is the compact extreme value theorem, checked in
`IsCompact.exists_isMaxOn` in the pinned source:
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/Order/Compact.lean

## Shared source chain and declaration bridges

- `maxModulus`: on the standard domain, a local representation of the
  standard construction (标准构造的本地表示). For continuous f and r≥0,
  the circle is compact and nonempty, and the continuous real function
  `z -> norm (f z)` has a greatest value. Its supremum equals that value,
  so the Lean expression agrees with the usual circular maximum.
  Separately, Lean's `sSup` is a total real-valued operation: the expression
  can be written for any function and any real radius. For r<0 the circle
  is empty; without continuity its norm image need not be bounded or attain
  its supremum. Total definability is not an assertion that these cases
  have a maximum in the usual sense.
- `max_modulus_zero`: the radius-zero circle is exactly `{0}`. Its norm
  image is the singleton `{norm (f 0)}`, whose real supremum is that value.
  This step requires no continuity or analyticity.
- `max_modulus_attained`: under exactly `Continuous f` and `0 <= r`, use
  compactness of the sphere, its nonemptiness, and continuity of `norm o f`
  in `IsCompact.exists_isMaxOn`. The attained greatest image value is an
  `IsLUB`; `IsLUB.csSup_eq` identifies it with `maxModulus f r`.
  No entire-function hypothesis is required. The cited paper's setting
  supplies notation, while compact extreme values supply this wider scope.

## What this note does and does not attest

Attested by this repository's own retrieval: the arXiv metadata and the
displayed section-2 notation in the PDF; the pinned extreme-value theorem
signature and the three local declaration signatures and proof bridges.

The round-19 classification is received from issue #6298. The paper is not
claimed to state the general continuous-function theorem. Any attribution
of that exact theorem to the paper remains `ASSUMED-UNVERIFIED`. The four
existing Citation entries bound to the repository's own square-shadow
atom are outside this note's assessment; their presence is not independent
external literature evidence.
