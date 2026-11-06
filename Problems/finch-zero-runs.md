---
slug: finch-zero-runs
bibkey: finch2026quadratic
doi: 10.48550/arXiv.2610.34300
url: https://arxiv.org/abs/2610.34300v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/FinchZeroRunsModThree.result
---

# Finch Remark 20: maximal zero-run attainment

## Problem

Steven Finch, *Three Quadratic Recurrences Modulo 3: What We Can Prove and
What We Can Guess*, arXiv:2610.34300v1, Remark 20, asks whether the upper
bound of `floor((k-1)/4)` gaps is always attained by a run of zeros spaced
exactly four apart. The binding statement includes a source sequence for
every `k ≥ 2`, and for every such sequence with `k mod 4 ∈ {0,1}` and a
positive bound it requires a run attaining that bound.

The recurrence is over `ZMod 3`, with `x n = 0` for `1 ≤ n < k`, `x k = 1`,
and `x n = x (n-1) + x (n-k)^2` for `n ≥ k+1`. A run starts at `r ≥ k+1`,
has positive gap count `g`, has zeros at `r, r+4, …, r+4g`, and has no other
interior zeros.

### Statement echo

The Lean `claim` preserves these source clauses literally. The settling
module's `result` is the literal proposition `¬ claim`.

## Motivation

The question is a universal attainment assertion separate from Finch's upper
bound. A certified counterexample at `k = 61` settles the universal assertion
while leaving the upper bound available for further work.

## Gap

The formal result supplies a source sequence at `k = 61`, a finite forward
invariant packed-state orbit, and a forbidden digit mask. The result does not
settle the upper bound of Theorem 16 or attainment parameters for other `k`.

## Route

Use the packed ternary transition retaining sixty digits. The explicit list
has 9685 states, contains the initial state, and is closed under the
transition; its terminal transition returns to entry 739. A fifteen-gap run
at `k = 61` would force an eleven-gap zero mask among the lowest 45 digits of
the state after `r-17` transitions. Every reachable state excludes that mask,
so the run cannot exist.

## Falsifier

The settlement would fail if the constructed sequence did not satisfy the
source recurrence, if the finite list were not closed for every transition, if
the orbit left the list, or if the run-to-mask implication failed for an
admissible start. The Lean kernel checks these obligations in the delivered
module.

## Evidence

The settling declaration is
`D5/S1/Recurrence/FinchZeroRunsModThree.result`, with frozen module statement
id `sha256:1d4aef3d14b78cc1b869626637f8cb05a47e32d784c14b93b4f5c67740ea3821`.
The source note is `Library/Digit/finch2026quadratic.md` and cites Finch,
arXiv:2610.34300v1. The supporting checker is recorded at
`the-omega-institute/trureturing-experiments` commit
`d960dc672a3b23118e6e542d41fdddddb6390d11`, path
`docs/reports/quadratic-recurrence-mod3-zero-runs/check.py`, SHA256
`fd75da0556d3f91a6cfd70f154b7c64ff785ede6f02d24ce90c601a03c0944a4`.
Its recorded command exits 0 with `ALL_CHECKS_OK`.

## Triage

### What the settlement shows

- **Proved:** for `k = 61`, the reachable orbit excludes the eleven-gap mask,
  and therefore no fifteen-gap run attains the proposed bound.
- **Computed and kernel-checked:** the certificate has exactly 9685 states and
  the terminal transition collides with state `S739 = S9685`.
- **Computed by checker, not used by the result:** a ten-gap witness occurs at
  `r = 2780`.
- **Open:** the upper bound in Theorem 16 and the attainment parameters for
  other values of `k`.

The settlement changes the universal attainment reading in Remark 20: it is
false as stated. It does not refute Theorem 16 or make a claim about the
remaining parameter values.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The result establishes the
formal refutation and makes no claim about originality or priority.
