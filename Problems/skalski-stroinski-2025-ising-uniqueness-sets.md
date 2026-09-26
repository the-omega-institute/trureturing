---
slug: skalski-stroinski-2025-ising-uniqueness-sets
bibkey: skalski2025level
doi: 10.48550/arXiv.2511.20925
url: https://arxiv.org/abs/2511.20925v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/IsingUniquenessSets.result
---

# Skalski and Stroiński's conjecture on the smallest set of uniqueness for the Ising cone

## Problem

Skalski and Stroiński work on `X = {-1,+1}^k` with the Rademacher functions
`r_j(x) = x_j` and the Walsh functions `w_L(x) = ∏_{j∈L} r_j(x)`; for
`1 ≤ q ≤ k` they set

> `B^k_q = Lin{w_L : L ⊂ {1,…,k} and |L| ≤ q}`.

Following Bogdan, Bosy and Skalski, a subset `U ⊂ X` is a set of uniqueness
for `(B^k_q)_+`, the nonnegative functions of `B^k_q`, if `φ = 0` is the only
such function vanishing on `U`, and `u(k,q)` is the size of the smallest one.
The section on extremal sizes closes with the conjecture

> `u(k,2) = k+1`, i.e., for every `k` there are no sets of uniqueness having at
> most `k` elements.

Issue #10022 fixes the readings: points of `X` are functions `Fin k → Bool`
with `true` read as `+1`; `B^k_2` is the real span of the `w_L` with
`|L| ≤ 2`; the equality is read for `k ≥ 3`, and the edge `k = 2` is recorded
separately.

## Motivation

The frozen declaration `D5/S3/Combinatorics/IsingUniquenessSets.result`
proves that no set of uniqueness for `(B^k_2)_+` has at most `k` points, for
every `k`; that `u(k,2) = k + 1` for every `k ≥ 3`; and that `u(2,2) = 4`.
Sets of uniqueness control the existence of maximum likelihood estimators in
the Ising exponential family, and `u(k,2)` is the sample size below which no
sample can guarantee it.

## Gap

Issue #10022 preregisters this published conjecture and its literature
check. Semantic Scholar reports zero citations of arXiv:2511.20925; Crossref
finds no journal version; MathDB `/p/371692` has status `open` with zero
solutions; an arXiv query for "set of uniqueness" returns only the source in
this sense. The source proves `u(k,2) ≤ k + 1` and a lower bound of order
`log k` from a covering argument.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent proof.

## Route

Lower bound, every `k`: if `|U| ≤ k`, the linear map sending
`v ∈ ℝ^{k+1}` to the values `v_0 + Σ_i v_i x_i` at the points `x ∈ U` has a
nonzero kernel vector. Since every coordinate squares to one, the square
`φ(x) = (v_0 + Σ_i v_i x_i)^2` is a combination of `w_∅`, the `w_{i}` and the
`w_{i,j}`, so `φ ∈ B^k_2`; it is nonnegative and vanishes on `U`, and it is not
identically zero, because comparing the all-plus point with the point where
coordinate `i` is flipped forces `v_i = 0` and then `v_0 = 0`. So `U` is not a
set of uniqueness.

Upper bound, `k ≥ 3`: let `e_m` (`f_m`) be the point whose only `+1` (`-1`)
coordinate is `m`. Every `φ ∈ B^k_2` satisfies

- `Σ_m φ(f_m) − Σ_m φ(e_m) + (k−2)(φ(−𝟙) − φ(𝟙)) = 0`,
- `Σ_m φ(e_m) + Σ_m φ(f_m) − (k−4)(φ(𝟙) + φ(−𝟙)) = 8·2^{−k} Σ_x φ(x)`,

as each `w_L` with `|L| ≤ 2` checks directly. If `φ ≥ 0` vanishes at every
`e_m` and at `𝟙`, the first identity forces `φ(−𝟙) = 0` and `φ(f_m) = 0`, the
second then gives `Σ_x φ(x) = 0`, and nonnegativity gives `φ = 0`. So these
`k + 1` points form a set of uniqueness.

Edge `k = 2`: `B^2_2` contains the indicator of every point, so only `X`
itself is a set of uniqueness and `u(2,2) = 4`.

## Falsifier

A refutation of the lower bound would be a set of at most `k` points on which
every nonnegative function of `B^k_2` vanishing there is zero; the square of an
affine function through a kernel vector rules this out. A refutation of the
equality for some `k ≥ 3` would need the `k + 1` points above to fail, which
the two linear identities exclude.

## Evidence

For `k = 3..8`, fifty random members of `B^k_2` each satisfy both identities
and `Σ_x φ(x) = 2^k c_0` to within `10^{-8}`; for twenty random sets of `k`
points per `k`, the kernel vector yields a nonzero square vanishing on the
set. At `k = 2`, the indicator of `(−1,−1)` is nonnegative and vanishes on the
three points of the source's Lemma rem:three. The Lean proof has only the
standard axiom closure `propext`, `Classical.choice`, and `Quot.sound`. These
finite checks support the reading but do not establish the universal theorem.

## Triage

First-tier external named open problem: Skalski and Stroiński,
arXiv:2511.20925v1 (2025), closing conjecture of the section on extremal sizes
of sets of uniqueness, preregistered in issue #10022. Resolution: `proved`,
with the equality read for `k ≥ 3`; at `k = 2` the source's own listing gives
`u(2,2) = 2^2 = 4`, which the delivered statement records.

The public surface is exactly `sgn`, `walsh`, `walshSpace`,
`IsSetOfUniqueness`, `minUniqueness`, `claim`, and `result`. This is a uniform
theorem, not bounded enumeration, checker infrastructure, numeric reduction,
or a certified finite instance, so `utility: none` applies.

## ASSUMED-UNVERIFIED

The linear-programming values `u(3,2) = 4`, `u(4,2) = 5`, `u(5,2) = 6`
reported by the screening search are not recomputed here. The bounded
literature check does not establish exhaustive worldwide novelty, priority, or
the absence of an independent proof. The Lean kernel does not authenticate the
external source, its version history, or the literature-check coverage. The
finite checks do not establish the universal theorem.
