---
slug: maier-2024-boson-ordering-stirling-closed-form
bibkey: maier2024bosonordering
doi: 10.48550/arXiv.2308.10332
url: https://arxiv.org/abs/2308.10332v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.result
---

# A closed form for the generalized Stirling numbers of boson ordering

## Problem

Maier uses the Hsu–Shiue generalized Stirling numbers to express orderings
of boson creation and annihilation operators. With
`(y)^{n, α} = y(y − α) ⋯ (y − (n − 1)α)`, the rescaled numbers
`Ŝ_{n,k}(α, β; r)`, `0 ≤ k ≤ n`, are defined by
`(βx + r)^{n, α} = Σ_k Ŝ_{n,k}(α, β; r) C(x, k)`, equivalently (Theorem 4.1)
`Ŝ_{n,k} = Σ_{x=0}^{k} (−1)^{k−x} C(k, x) (βx + r)^{n, α}`. Conjecture 5.3 of
arXiv:2308.10332v4 states, as found heuristically:

> For all r ∈ ℤ,
> Ŝ_{n,k}(−1, 2; r) = Σ_{j=⌊(2−r)/2⌋}^{⌊(n+2−r)/2⌋} C(n − j, n − k) n! C(n + 1, 2j + r − 1).

The source remarks that the upper argument `n − j` may be negative. Issue
#10170 fixes the readings: `n, k ∈ ℕ` with `k ≤ n`, `r ∈ ℤ`; `Ŝ` is the
finite sum of Theorem 4.1 with the rising factorial; `C(n − j, n − k)` is the
generalized binomial coefficient `Ring.choose`; the sum runs over integers `j`
between the stated floors.

## Motivation

The numbers `Ŝ_{n,k}(−1, 2; r)` enter the ordering identities of §6 of the
source. The frozen declaration
`D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.result` proves the
conjectured closed form for every `n`, every `k ≤ n` and every integer `r`.

## Gap

Issue #10170 preregisters the conjecture and its literature check. arXiv lists
version 4 (2024-02-09) with the journal reference Adv. in Appl. Math. 156
(2024) 102678. Semantic Scholar reports two citing papers: a paper on
squeezing in mesoscopic circuits, and arXiv:2508.13094 by the same author,
whose source cites only Theorem 6.5 of the paper.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent proof.

## Route

Extend the sum to all integers `j`; outside the stated range the factor
`C(n + 1, 2j + r − 1)` vanishes. Write `L(n, k, r)` for the left side and
`R(n, k, r)` for the sum divided by `n!`.

- (K) `L(n, k + 1, r) = L(n, k, r + 2) − L(n, k, r)`, because the forward
  difference in `x` commutes with the shift `x ↦ x + 1`, which replaces `r` by
  `r + 2`. The same holds for `R` when `k < n`: shifting `j` by one and Pascal's
  rule `C(a + 1, b + 1) = C(a, b) + C(a, b + 1)` for the generalized binomial
  coefficient give `R(n, k, r + 2) − R(n, k, r) = R(n, k + 1, r)`.
- (R) At `k = 0`, `L(n, 0, r) = r(r + 1) ⋯ (r + n − 1)`, and
  `L(n + 1, 0, r) − L(n + 1, 0, r − 1) = (n + 1) L(n, 0, r)`. Pascal's rule for
  `C(n + 2, ·)`, a shift of `j` and Pascal's rule for the generalized binomial
  coefficient give `R(n + 1, 0, r) − R(n + 1, 0, r − 1) = R(n, 0, r)`.
- At `r = 1` both sides equal `n!`: only `j = 0` contributes to `R(n, 0, 1)`.
  Induction on `n`, with an integer induction on `r` from `r = 1`, gives the
  case `k = 0`; for `n = 0`, `R(0, 0, r) = 1` because exactly one `j` has
  `2j + r − 1 ∈ {0, 1}`. Induction on `k` using (K) gives every `k ≤ n`.

## Falsifier

The identity fails if the first binomial coefficient is read as zero for a
negative upper argument: at `(n, k, r) = (1, 1, −1)` the left side is `2`
while that reading of the right side gives `1`. The source's remark that the
upper argument may be negative fixes the generalized reading.

## Evidence

Exact integer computation confirms the identity with the generalized binomial
coefficient for `n ≤ 10`, `0 ≤ k ≤ n`, `|r| ≤ 25` (3366 cases), and finds 1276
failures in the same range under the zero-for-negative-upper-argument reading.
The first rows at `r = 0` are `1`; `0, 2`; `0, 6, 8`; `0, 24, 72, 48`;
`0, 120, 600, 864, 384`.

The canonical source is
`D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.lean`. Its public
declarations are `stirlingHat`, `conjectureSum`, `claim`, and `result`; `cz`,
`fB` and `B` are private non-proposition definitions. The frozen module state
has statement identity
`sha256:e320e22b1bf106ac6f0aad4594870baad8dafd57feb4e6ab71d8e7b6bd899e89`.
The result declaration has statement identity
`sha256:297d337df538c5c402555676c2199e22ec0e82a59ad18bbb66bd1b12ac7d72c2`.
The Freeze event is
`sha256:c85ed53a42d5a1871592dbc6612a8f15c84ea5ecd58e16d806cf277ccff0af81`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #10170 before the
probe. `theorem`; resolution `proved` under the generalized-binomial reading.
The public theorem has `proof_shape: content`: the recursions (K) and (R) for
the conjectured sum and the layered induction are new propositions on the
live proof path, not instances of pinned lemmas. Its escape witness is form
(2), the public conclusion itself, and its admission basis is
`open-problem-resolution`. Utility `none`: it is a theorem for every `n`, `k`
and `r`.

## ASSUMED-UNVERIFIED

Whether the journal version keeps the conjecture and its number was not
checked. The bounded literature check does not establish exhaustive worldwide
novelty, priority, or the absence of an independent proof. The Lean kernel
does not authenticate the external source or its version history.
