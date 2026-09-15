---
slug: kreh-2015-minimal-sets-conjecture-18
bibkey: kreh2015minimalsets
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf
triage: theorem
motivation_gids:
  - D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation
---

# Refutation of the divergence sentence in Kreh's Conjecture 18

## Problem

Definition 16 (Unicode transcription, preserving the printed superscripts):

> Definition 16. For a given set M ⊂ N define a sequence δⁿ(M) of sets recursively by δ⁰(M) := M, δ(M) := δ¹(M) := M \ S(M), δⁿ⁺¹(M) := δ(δⁿ(M)) and let ηⁿ(M) := |S(δⁿ(M))|, η(M) := η¹(M).

Conjecture 18 (Unicode transcription, preserving the printed superscripts):

> Conjecture 18. There are only countably many infinite sets M ⊂ N with η(M) ≤ η⁰(M). For all other sets we have ηⁿ(M) → ∞.

Kreh writes `N` for the positive integers, writes `x ⊳ y` when the decimal
string of `x` is obtained from that of `y` by deleting zero or more digits,
and writes `S(M)` for the elements of `M` minimal under that order. The Lean
definition `digitSubseq a b` is `a ⊳ b`; `minimal`, `peel`, and `eta` are
Kreh's `S`, `δ`, and `η` constructions.

The literal refuted statement is the second sentence: for every infinite set
`M` of positive natural numbers with `eta M 0 < eta M 1`, every natural bound
`B` eventually satisfies `B ≤ eta M k` at every later layer. This is exactly
`claim`, including the explicit positivity premise. Lean's `Set.ncard` is zero
on an infinite set, but that convention is never used in the refutation:
every displayed minimal layer is proved to be a singleton or a pair. That
theorem does not address the first sentence, concerning countably many
infinite sets with `η(M) ≤ η⁰(M)`. A companion result for that sentence is
described below; this dossier's resolution binding remains the divergence
theorem.

## Motivation

The divergence sentence asserts a universal asymptotic consequence from the
first two layer sizes. An explicit infinite set whose first two layers have
sizes one and two while every later layer has size one settles that sentence
without making any assertion about Kreh's separate countability sentence.

## Gap

Preregistration issue #7639 and its probe report record searches dated
September 14, 2026. The publisher PDF and publisher TeX were read, and both
locate Definition 16 and Conjecture 18 on page 14 of the PDF. The Semantic
Scholar record reported `citationCount = 0` and an empty citation list. The
full texts of Jeffrey Shallit's 2001 "Minimal primes" and the
Bright-Devillers-Shallit "Minimal elements for the prime numbers" paper have
no hit for Kreh or Conjecture 18; both predate the 2015 conjecture. The
MathOverflow API returned 0 results, GitHub exact-identifier searches returned
0 results, and Crossref bibliographic search found no DOI for the paper.

Google Scholar was blocked by a CAPTCHA, the arXiv API returned HTTP 503, and
the OpenAlex quota was exhausted; those surfaces are `ASSUMED-UNVERIFIED`.
All completed searches were bounded. No priority claim is made.

## Route

Let `u j = 110*10^j` and
`M* = {1, 10, 11} ∪ {u j : j ∈ ℕ}`.

First, the printed decimal digits satisfy
`digits(u j) = [1, 1, 0] ++ replicate j 0`. Hence
`digitSubseq (u i) (u j)` holds exactly when `i ≤ j`; 10 and 11 are
incomparable, while 1, 10, and 11 are subsequences of every `u j` as
appropriate.

Second, `minimal M* = {1}`. After removing it, the remaining set is
`{10, 11} ∪ range u`, whose minimal set is `{10, 11}`.

Third, induction on `k` proves that `peel M* (k+2)` is the tail
`{u (k+j) : j ∈ ℕ}` and that its minimal set is `{u k}`.

Finally, `eta M* 0 = 1 < 2 = eta M* 1`, while
`eta M* (k+2) = 1` for every `k`. Taking `B = 2` contradicts the asserted
eventual lower bound and proves `result : ¬ claim`.

## Falsifier

The refutation would fail if the decimal expansion of `110*10^j` did not have
the stated trailing-zero form, if subsequence comparability among the `u j`
did not agree with index order, if 10 and 11 were comparable, if either of the
first two minimal sets differed from `{1}` and `{10, 11}`, if removing `{u k}`
did not advance the infinite tail, or if the positivity or infinitude premises
failed for `M*`.

## Evidence

- Lean module:
  `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- A hot-tree kernel profile at the implementation head gave wall time
  `9.82 s`, cumulative type checking `80.2 ms`, and maximum resident set size
  `1,599,176,704 bytes`.
- The orchestrator's truncation `M*_J` with `J = 8` has 12 members and layer
  sizes `[1,2,1,1,1,1,1,1,1,1,1,0]`; the final zero is truncation exhaustion.
  It also checked `u_i ⊳ u_j` exactly when `i ≤ j` for `i,j ≤ 5`, found 10
  and 11 incomparable, and found both subsequences of 110.
- The probe independently obtained 12 members and
  `[1,2,1,1,1,1,1,1,1,1,1,0]` for `J = 8`; for `J = 12` it obtained 16
  members and `[1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,0]`. Its pairwise check of
  `u_i ⊳ u_j` exactly when `i ≤ j` for `0 ≤ i,j ≤ 8` had 0 mismatches.

The finite truncations expose the intended pattern but do not carry the
theorem. The Lean proof classifies the decimal subsequence order and proves
the tail invariant for every natural layer.

### Related result for the first sentence

`D5/S1/Digit/KrehMinimalSetCountabilityRefutation.result` states that the
collection of infinite positive sets satisfying `eta M 1 ≤ eta M 0` is
uncountable. For every `A : Set ℕ`, it uses
`F_A={1,6} ∪ {16·10^(2n) : n ∈ ℕ} ∪ {16·10^(2n+1) : n ∈ A}`.
The first two minimal sets are exactly `{1,6}` and `{16}`. The even indices
ensure infinitude, and the odd indices recover `A`, giving the powerset
injection required by Cantor's theorem.

Theorem 14 and Examples 15 and 17 of the source already provide the two-seed
chain mechanism with sizes `2,1,1,...`; the companion result adds the
explicit powerset encoding and uncountability deduction. The shared
`Library/Digit/kreh2015minimalsets.md` records that distinction and the
bounded literature findings. This supplementary clause uses the same
Conjecture 18 identity and adds no distinct-question count or second
resolution binding.

## Triage

`theorem`. The formal result refutes only the divergence sentence of
Conjecture 18 by an infinite symbolic counterexample. The module is classified
`utility: none`: `digitSubseq`, `minimal`, `peel`, `eta`, and `claim` are
definitions, while `result` is an infinite-set construction with induction
over all layers. None of `bounded-enumeration`, `checker`,
`numeric-reduction`, or `certified-instance` applies.

## ASSUMED-UNVERIFIED

Google Scholar was blocked by a CAPTCHA, the arXiv API returned HTTP 503, and
the OpenAlex quota was exhausted. The literature and repository searches were
bounded. The orchestrator and probe numerical readings above were supplied by
issue #7639 and were not recomputed by this implementation seat. No claim is
made by the divergence theorem about the countability sentence, a general
structure theorem for minimal sets, an OEIS binding, or priority. For the
companion countability result, the fully reviewed supplied 2016 preprint
*Deleting Digits*, arXiv:1607.01548v1, contains no explicit resolution of
this sentence. The 2017 version-of-record PDF (DOI 10.1017/mag.2017.6)
returned HTTP 403 and its contents remain `ASSUMED-UNVERIFIED`; the read-scope
finding does not certify absence of a later resolution or worldwide priority.
