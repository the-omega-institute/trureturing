---
bibkey: finch2026quadratic
authors: Steven Finch
year: 2026
title: "Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess"
doi: 10.48550/arXiv.2610.34300
url: https://arxiv.org/abs/2610.34300v1
claim: "Remark 20 asks whether the upper bound of floor((k-1)/4) gaps is always attained by a run of zeros spaced exactly four apart."
strata_touched:
  - D5/S1/Recurrence/FinchZeroRunsModThree
license: citation-only
triage: anchor
---

# Finch's quadratic recurrences modulo three

## Verified locator

DOI: 10.48550/arXiv.2610.34300

Source: https://arxiv.org/abs/2610.34300v1

## Source statements

Page 6:

> As in the main paper, fix k ≥ 2 and let x₁, x₂, ··· ∈ ℤ/3 be given by
>
> x₁ = ··· = xₖ₋₁ = 0, xₖ = 1, xₙ = xₙ₋₁ + xₙ₋ₖ² (n ≥ k + 1).

Definition 15, pages 6–7:

> Let r ≥ k + 1 and g ≥ 1 be integers. We say that x has a run of zeros spaced
> exactly 4 apart, with g gaps, starting at r, if
>
> 1. xᵣ = xᵣ₊₄ = xᵣ₊₈ = ··· = xᵣ₊₄g = 0, and
> 2. xₙ ≠ 0 for every other n with r < n < r + 4g.

> The number g counts the gaps, not the zeros.

The example r,r+4,r+8,r+11 has two gaps in the first run. No condition is
imposed before its first zero or after its last zero.

Remark 20, page 8:

> Empirical data suggest that Theorem 16 is the best possible. For instance,
> runs with exactly ⌊(k−1)/4⌋ gaps were observed for k = 245, 297, 333 (where k ≡ 1)
> and for k = 288, 320, 340 (where k ≡ 0). Proving that such maximal runs always occur
> would be a nice exercise in experimentation, but maybe a hard one in theory!

The universal attainment reading is the target of issue
[#23013](https://github.com/the-omega-institute/trureturing/issues/23013).
It includes existence of a source sequence for each k≥2 and attainment for
every source sequence when k modulo four is zero or one and the bound is
positive. Natural index zero is unused. Natural division renders the floor.
The upper bound of Theorem 16 and Conjectures 14 and 23 are separate claims.

## Refutation and limits

The repository refutation uses k=61. Its packed ternary orbit has a
forward-invariant list of 9685 states, with the last transition returning to
entry 739. Every listed state rejects the eleven-gap zero mask, so a
fifteen-gap run cannot occur in the constructed source sequence. This is a
refutation of universal attainment; it does not contradict Theorem 16.

The supporting experiment is in
`the-omega-institute/trureturing-experiments`, commit
`d960dc672a3b23118e6e542d41fdddddb6390d11`, at
`docs/reports/quadratic-recurrence-mod3-zero-runs/check.py` (SHA256
`fd75da0556d3f91a6cfd70f154b7c64ff785ede6f02d24ce90c601a03c0944a4`).
The recorded command is
`python3 docs/reports/quadratic-recurrence-mod3-zero-runs/check.py`, exit 0,
ending with `ALL_CHECKS_OK`. It also finds a ten-gap run at r=2780; that
supporting calculation is separate from the settling theorem.

The literature screen in #23013 found no settlement within its successfully
read sources. Completeness is ASSUMED-UNVERIFIED: OpenAlex and live Zenodo
queries were unavailable, and the Google response did not expose usable
results. Finch's earlier k=61 period value is not claimed as new.
