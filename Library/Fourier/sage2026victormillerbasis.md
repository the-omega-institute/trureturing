---
bibkey: sage2026victormillerbasis
authors: "The SageMath Developers"
year: 2026
title: "The Victor Miller basis (SageMath reference manual)"
doi: null
url: https://doc.sagemath.org/html/en/reference/modfrm/sage/modular/modform/vm_basis.html
claim: "The classical normalized level-one Miller basis is constructed from standard modular-form generators and has integer q-expansions."
strata_touched:
  - D5/S3/Arith/ModularForms/IntegralMillerBasis
license: citation-only
triage: anchor
---

# Classical level-one Miller normalization

## Verified locator

Source: https://doc.sagemath.org/html/en/reference/modfrm/sage/modular/modform/vm_basis.html

The source is the SageMath reference manual's page **The Victor Miller
basis**, specifically its introductory normalization and the function
`victor_miller_basis(k, prec=10, cusp_only=False, var='q')`.
The year records inspection of the live reference page, not a separate
publication date. The inspected HTML has SHA256
`182323035c7e4aef97160d32283154f7dd637b1cb04dab0727f5c24fa55a6c4a`.

The introduction describes the normalized coefficient basis and computation
using standard generators of the level-one ring. The function documentation
states that its output power series are in `ZZ[[var]]`; with `cusp_only=True`
it returns a basis of the cuspidal subspace. Its weight-24 cusp example begins
with `q+195660*q^3+12080128*q^4` and
`q^2-48*q^3+1080*q^4`. This identifies the classical result and normalization;
it is not Lean evidence and does not specify this project's recursion.

The project constructs actual Mathlib cusp forms at weights `12m+s`, with
`m>=1` and `s` one of `0,4,6,8,10,14`. It proves the integer recursion's
all-coefficient analytic equality, first-m normalization, exact dimension,
uniqueness, full integer coefficient lattice equivalence and the optimality
of m initial integrality checks. The general coefficient and lattice APIs
belong to that stated positive-dimensional range. Empty cusp spaces and
an all-weight Hecke algorithm are outside this module's delivered scope.

The pinned formal suppliers are Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`:
`CuspForm.discriminantEquiv` and
`ModularForm.dimension_level_one` in
`NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`, together with
its normalized Eisenstein and discriminant suppliers documented in
`Library/Fourier/mathlib2026modularforms.md`.

This is a formal construction of classical infrastructure. The exact Lean
realization, integer recursion, sharpness witness and lattice coordinate
bridges are repository proofs; no mathematical originality, new Maeda case
or solution of an external open problem is claimed. No source text or code
is vendored.
