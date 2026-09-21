---
slug: chu-2026-schreier-multiset-recurrence-q-two
bibkey: chu2026schreiermultisets
doi: 10.5281/zenodo.19949535
url: https://math.colgate.edu/~integers/aa53/aa53.pdf
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.result
---

# The first q = 2 Schreier-multiset recurrence

## Problem

Chu, Geng, King, Miller, Tresch, and Vasseur define on printed page 19:

> A^{(s)}_{p,q,n} := {F ⊂ {1, …, 1, …, n − 1, …, n − 1, n} : n ∈ F and q min F ≥ p|F|}

In the printed display, an underbrace labelled `s` spans the copies of each
entry from `1` through `n − 1`: there are `s` copies of every one of those
entries, followed by one copy of `n`. The page then says:

> Below are the data and conjectured recurrences we gather:

Its first item is:

> (|A^{(2)}_{1,2,n}|)^∞_{n=1}: 1, 2, 4, 9, 19, 41, 88, 189, 406, 872, 1873, 4023, 8641, . . . with a_n = a_{n−1} + 2a_{n−2} + a_{n−3};

The formal reading makes three decisions. First, `s = 2` means two copies of
each of `1,...,n−1` and one copy of `n`. Second, `(p,q) = (1,2)` means
`2 · min F ≥ |F|`, with `min F = F.toFinset.min'` on the witness `n ∈ F`
and `|F| = Multiset.card`. Third, the recurrence starts at `4 ≤ n`, the least
index for which all four sequence indices are at least one; at the boundary,
`a_4 = 9 = a_3 + 2a_2 + a_1`.

## Motivation

The source prints thirteen terms and labels the recurrence conjectural. The
frozen declaration
`D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.result` proves the
recurrence for every natural `n ≥ 4`, rather than only for the displayed data.

## Gap

Issue #9284 preregisters this first-tier published conjecture and the bounded
literature check. OpenAlex record `W4414762075` has `cited_by_count = 0`.
The full texts arXiv:2506.14312, arXiv:2606.21865, arXiv:2608.18874, and
arXiv:2304.05409 were checked; none proves or refutes item 1, and Section 7 of
arXiv:2608.18874 restates the general problem as open in August 2026. OEIS
A141015 carries the numerical recurrence but gives no Schreier-multiset
interpretation; items 2--5 of Section 5 were absent from the OEIS searches.
Three MathDB queries returned no entry. Semantic Scholar returned HTTP 429 and
is `ASSUMED-UNVERIFIED`.

These readings are `not-found-in-searched-scope`; they do not establish
exhaustive worldwide literature coverage, publication priority, or the absence
of an independent proof.

## Route

The live escape witness (W) is the bridge identity

`a n = c (2n−2) + c (2n−1)` for every `n ≥ 1`,

where `c T` counts ordered compositions of `T` with parts in `{2,3,4}`. To
construct the bijection, fix `|F| = k`; then `min F ≥ ⌈k/2⌉`, and
`F \ {n}` is a card-`(k−1)` sub-multiset of the ground restricted to
`{⌈k/2⌉,…,n−1}`. It is encoded as the composition
`(2 + count F (t + r))_r`, whose parts lie in `{2,3,4}`. By sending each part to
its letter plus two, `c T` is also the preregistered sum `Σ_j N(j,T−2j)`.

Removing the first part gives
`c T = c (T−2) + c (T−3) + c (T−4)` for every `T ≥ 4`. Applying this identity to the two
composition counts in (W), and then using additive algebra, gives the stated
order-three recurrence.

Under CLAUDE.md Section 3.2, `result` has `proof_shape: content`. The bridge
identity lies in the elaborated proof of `result`; it is proved by the live
encode/decode bijection, is not obtained from a frozen or pinned-upstream
statement by instantiation, projection, or normalization, is not definitionally
equivalent to the final recurrence, and is consumed by the four adjacent-count
identities in the final derivation. The bypass test found no route from existing
frozen or pinned-upstream statements to the conclusion without this new
combinatorial construction. The module basis is `open-problem-resolution`
under the preregistration in issue #9284.

## Falsifier

A refutation would be an `n ≥ 4` with
`a_n ≠ a_{n−1} + 2a_{n−2} + a_{n−3}`. The exact sweep through `n = 40`
found no such index.

## Evidence

Brute-force sub-multiset enumeration through `n ≤ 10` and the independent
min/size decomposition count through `n ≤ 40` agree termwise. The thirteen
printed terms match, and the recurrence holds for every checked
`4 ≤ n ≤ 40`. The computed prefix is

`a_1..a_16 = 1, 2, 4, 9, 19, 41, 88, 189, 406, 872, 1873, 4023, 8641, 18560, 39865, 85626`.

The source wording and printed-page locator are recorded in
`Library/Recurrence/chu2026schreiermultisets.md`. The Lean proof uses only the
standard axiom closure `propext`, `Classical.choice`, and `Quot.sound`. Its
Freeze event has no prerequisite frozen project nodes.

## Triage

First tier: item 1 in Section 5 of Chu--Geng--King--Miller--Tresch--Vasseur,
*Integers* 26 (2026), #A53, preregistered in issue #9284. Resolution: `proved`.

| proof_shape | escape_witness | direct frozen dependencies | admission_basis |
| --- | --- | --- | --- |
| content | (W) | none | open-problem-resolution |

The public surface is exactly `ground`, `A`, `a`, `claim`, and `result`; the
five data definitions `comps`, `c`, `encode`, `decodeFrom`, and `decode` are
private. This is a symbolic theorem for every `n ≥ 4`, not bounded enumeration,
checker infrastructure, numeric reduction, or a certified finite instance, so
`utility: none` applies. Items 2--5 of Section 5 are not asserted.

## ASSUMED-UNVERIFIED

Semantic Scholar is `ASSUMED-UNVERIFIED` because it returned HTTP 429. The
bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof. The Lean kernel does not
authenticate the external PDF, its printed pagination, the literature-search
coverage, or publication history. The finite exact checks through `n = 40` do
not establish the universal theorem.
