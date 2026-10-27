---
bibkey: kitware2026minmax
authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, Claude Fable 5, and Claude Opus 5
year: 2026
title: The min--max theorem for approximation numbers
doi: null
url: https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean
claim: For bounded complex-linear maps between complete complex inner-product spaces with independent universes, every nonnegative strict threshold below the zero-based rank-bound approximation number admits n+1 independent vectors whose span has a uniformly larger lower modulus.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# The min--max theorem for approximation numbers

This note identifies four selected Lean source files in the public
AIQ-Kitware/aiq-dkps-formalization repository, at immutable revision
`8924c4cc743d2f193bb4f39bee800790698a681b`. The title is the module heading in
`ApproximationNumber/MinMaxUpper.lean`; the authors are the union of the
four selected file headers, not an attribution of unrelated repository
content. The source headers give the copyright year 2026 and release
these four files under Apache 2.0. No DOI is supplied by this citation.

The zero-based approximation number is the real infimum of
`norm(T - R)` over bounded linear maps `R : E →L[ℂ] F` whose cardinal
rank is at most the natural index `n`. The definition needs the two
normed additive-group and complex inner-product structures, and does
not need completeness. The min-max theorem assumes completeness of
both carriers. For `0 ≤ r < a_n(T)`, it constructs `s > r` and
`n + 1` complex-linearly independent vectors such that
`s * norm(x) ≤ norm(T x)` throughout the complex span of their range.
The source and target universe levels remain independent. No
compactness, separability, finite-dimensionality, nontriviality,
common-universe, or index-below-dimension premise is added.

The proof uses the positive square root of the Gram operator, the
positive-part cutoff and cocutoff from continuous functional calculus,
and the closed cutoff kernel with its orthogonal complement. A
rank-versus-error dichotomy either yields the independent family or
contradicts the strict threshold using the actual finite-rank
orthogonal-projection approximant. A self-adjoint cutoff is not
claimed to be an idempotent projection.

This is reuse of published mathematics. A native integration into a
different pinned Lean/Mathlib environment is not a novelty claim or a
proof of any compact-spectral-tail, ensemble, or roof-equality result.
The full original license, selected-source attribution, verbatim file
headers and change notice accompany the adapted proof in
`docs/reports/licenses/hilbert-approximation-minmax-third-party.md`.
The license statement here applies only to the four selected files.

## Verified locator

The exact selected min-max statement is at
https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean
in `ContinuousLinearMap.exists_linearIndependent_lowerBound_of_lt_approximationNumber_complex`.
The revision is `8924c4cc743d2f193bb4f39bee800790698a681b`. The four selected
sources are:

- `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean`: Approximation-number definition and rank-bound infimum. Header authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh.
  https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean
- `ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean`: Rectangular operator modulus and its norm identity. Header authors: Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking.
  https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean
- `ForTauCeti/Analysis/InnerProductSpace/Spectral/Cutoff.lean`: Positive-part spectral cutoff and cocutoff estimates. Header authors: Jon Crall, Claude Opus 5.
  https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/InnerProductSpace/Spectral/Cutoff.lean
- `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`: Strict-threshold min-max independent-family construction. Header authors: Jon Crall, Claude Opus 5.
  https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean

The original complete license is
https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/LICENSE.
The Basic and OperatorModulus source provenance credits are retained
with the selected-source notices; the cutoff and min-max source
attribute their continuous-functional-calculus proof in place. This
note does not select or license vendor/lean, SchurHorn or Singular.Subspace.
