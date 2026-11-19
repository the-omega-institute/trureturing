---
slug: oeis-a386705-equal-binary-run-sum-recurrence
bibkey: oeis2025a386705
doi: null
url: https://oeis.org/A386705
triage: theorem
motivation_gids:
  - D5/S1/Digit/EqualBinaryRunBridge
---

# A386705: sums of equally paired maximal binary runs

## Problem

Paolo Xausa's OEIS A386705 NAME, verbatim:

> a(n) = sum of the 2^(n-1) even positive integers having bit length 2*n and in which, when written in binary, each run of 0's is of exactly the same length as the run of 1's immediately before it.

Its FORMULA, verbatim:

> Empirical: a(n) = 12*a(n-1) - 36*a(n-2) + 32*a(n-3), with a(1) = 2, a(2) = 22, a(3) = 192.

For every integer index n >= 1, let S_n contain all positive even integers
whose canonical binary representation has length exactly 2*n and whose
maximal zero runs have the same lengths as their immediately preceding
maximal one runs. Define a(n) as the sum of the distinct integers in S_n.
The single assertion is the conjunction of the three stated initial values
and the displayed recurrence for every integer n >= 4, with values and
recurrence arithmetic in the integers.

The immutable source is
https://raw.githubusercontent.com/oeis/oeisdata/30c383550c8059b1712df8e32827d3b203765933/seq/A386/A386705.seq.
Its 1307 bytes have SHA256
`ee3c1a07327bdc5f3939c1c23317667770f7130bb5b14c1a9e40bcec92127efb`.
The exact event and quantifiers are fixed in
[the original preregistration](https://github.com/the-omega-institute/trureturing/issues/30525#issuecomment-6883156512).

## Motivation

The empirical formula concerns a sum over actual integers, not a sequence
defined by a recurrence. Proving it requires preserving canonical binary
representation, maximal runs and distinctness through the encoding. The
source credits the composition relation to A166751; that relation is a known
ingredient, not a new observation claimed here.

## Gap

The pinned record labels the full recurrence empirical. The bounded source
qualification in [issue #30525](https://github.com/the-omega-institute/trureturing/issues/30525)
and `Library/Digit/oeis2025a386705.md` found no exact solution in the inspected
arXiv identifier results, repository and pinned Mathlib searches, or GitHub
repository metadata queries. Loogle returned 403, GitHub code search 401 and
grep.app 429; those failures establish capability gaps, not absence of proofs.
The known composition correspondence alone does not provide the weighted
sum recurrence.

## Route

The literal predicate uses `(Nat.digits 2 m).reverse` and Boolean-equality
`List.splitBy`, so its runs are canonical maximal runs. The theorem
`D5/S1/Digit/EqualBinaryRunBridge.mem_row_iff` proves that membership is
equivalent to a unique list of strictly positive paired-run lengths summing
to n. Decoding is injective on these lists. The finite row bound omits no
literal member, and injective sum transport preserves each integer value
and counts it once.

Writing W(n) for the sum of decoded composition words, T(n) for the sum of
their decoded tails, E(n) for the sum of 2^k*4^r over first part k and tail
sum r, and U(n)=4^n*2^(n-1), the proof splits compositions of n+1 into the
disjoint images of prepending 1 and incrementing the first part. It derives
W(n+1)=5W(n)+2U(n)+2E(n)-3T(n), T(n+1)=W(n)+T(n),
E(n+1)=2U(n)+2E(n) and U(n+1)=8U(n), for n >= 1.
The initial data yield W(n)-T(n)+E(n)=U(n). Eliminating the auxiliary sums
gives the stated third-order recurrence. Sum transport identifies W(n) with
the original a(n); no recurrence is assumed to define a.

## Falsifier

A positive even integer of canonical bit length 2*n with the prescribed
maximal runs but missing from the finite row would contradict
`D5/S1/Digit/EqualBinaryRunBridge.mem_row_iff`. An initial-value discrepancy,
or an integer index n >= 4 violating the recurrence for the literal
distinct-integer sum, would contradict
`D5/S1/Digit/EqualBinaryRunBridge.full_claim`.

## Evidence

The formal source is `D5/S1/Digit/EqualBinaryRunBridge.lean`. Its `FullClaim`
is the complete conjunction, proved unconditionally by `full_claim`.
Natural indices cover all positive integer indices; n >= 4 ensures every
shifted index is positive. Sequence values and subtraction are in Z.
The axiom closure is limited to `Classical.choice`, `Quot.sound` and
`propext`, with no `sorryAx` or new axiom.

Both public theorems have typed four-slot registrations in
`Reg/D5/S1/Digit/EqualBinaryRunBridge.lean`. The existing support registrations
remain in `Reg/D5/S1/Words/DoubleTailShuffleSupport.lean`. Their continuation
is explicitly unknown; it establishes neither undecidability nor an
inexhaustibility claim. The Blueprint's typed `Proved` claim names only
`D5/S1/Digit/EqualBinaryRunBridge.full_claim`.

## Triage

Tier 1 external named empirical OEIS assertion, with a complete universal
symbolic proof. The admission basis is `open-problem-resolution`, using
the original source-bound preregistration on #30525. `full_claim` and
`mem_row_iff` have `proof_shape: content`. Bind-only auxiliary declarations
have actual consumers in the same proof; they supply no independent
admission basis. Utility is `none`: this is an unbounded symbolic theorem,
not an enumerated positive instance or a numerical reduction.

### What the settlement shows

- **Proved by `D5/S1/Digit/EqualBinaryRunBridge.full_claim`:** all three
  initial values and every n >= 4 instance of the exact literal-set
  recurrence hold. The decisive mechanism is injective sum transport
  followed by the composition split and weighted invariant.
- **Proved by `D5/S1/Digit/EqualBinaryRunBridge.mem_row_iff`:** positive
  even canonical words satisfying the maximal-run condition have unique
  strictly positive paired-run encodings. This bridge prevents omitted or
  duplicated integers in the sum.
- **Open in this delivery:** minimal recurrence order, asymptotics,
  alternative bases and unequal run ratios. No relaxation of the positive,
  even, canonical-length or maximal-run conditions is asserted. The theorem
  is an exact identity, so no approximation or sharp error bound is claimed.
- **Source dependency boundary:** the result supplies the empirical row-sum
  formula for the A166751-related rows. It neither changes the known
  composition correspondence nor certifies other formulas or related
  sequences. No dependency of another named open question on this formula
  is established in the inspected source scope.

## ASSUMED-UNVERIFIED

Worldwide priority, exhaustive absence of prior proofs, and semantically
equivalent solutions outside the bounded search remain unverified.
Unavailable search endpoints do not support a global openness claim.
Mathematical proof and typed resolution metadata do not certify publication,
remote required checks, integration or delivery credit.
