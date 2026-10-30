---
slug: oeis-a284005-kurkov-lower-bit-recurrence
bibkey: kurkov2019a284005
doi: null
url: https://oeis.org/A284005
triage: theorem
motivation_gids:
  - D5/S1/Digit/KurkovLowerBitRecurrence
---

# Kurkov's full lower-bit recurrence for A284005

## Problem

This dossier anchors exactly the November 10, 2019 FORMULA in
[OEIS A284005](https://oeis.org/A284005), attributed to Mikhail Kurkov:

> Conjecture: a(n) = 2*a(f(n)) + Sum_{k=0..floor(log_2(n))-1} a(f(n) + 2^k*(1 - T(n,k))) for n > 1 with a(0) = 1, a(1) = 2, f(n) = A053645(n), T(n,k) = floor(n/2^k) mod 2. - _Mikhail Kurkov_, Nov 10 2019

The NAME defines `a(n)=(1+A000120(n))*a(floor(n/2))` for `n>1`.
The initial data begins `1,2,4,6,8,12,18,24`, including `a(1)=2`.
Here `wt(n)=A000120(n)` is binary digit sum, `L=floor(log_2(n))`,
and removing the leading binary one gives `f(n)=n-2^L`.
All operations in the formal statement are natural-number operations.
Every index `0 <= k < L` occurs: an existing one bit contributes
`a(f(n))`, and these repeated contributions are retained.

The exact native result is:

```lean
theorem result :
    a 0 = 1 ∧ a 1 = 2 ∧
    (∀ n : ℕ, 1 < n → a n = (1 + wt n) * a (n / 2)) ∧
    (∀ n : ℕ, 1 < n →
      a n = 2 * a (n - 2 ^ Nat.log 2 n) +
        ∑ k ∈ Finset.range (Nat.log 2 n),
          a (n - 2 ^ Nat.log 2 n + 2 ^ k * (1 - n / 2 ^ k % 2)))
```

This includes `n=2` and every power of two. The lower-bit identity
asserts nothing at zero or one. The April 24, 2023 two-parameter
binomial conjecture and the A329369 modulo-two binomial transform are
distinct questions. The divisor-count representation in the entry's
NAME is outside this result.

## Motivation

The defining recurrence follows successive binary prefixes. The
question relates their product to setting each lower bit, while
preserving the multiplicity of contributions from bits already equal
to one. Its quantifier ranges over every natural index greater than one.

## Gap

The original-entry and history reading, attribution, repository
issue/comment reading, and bounded resolution searches described in
`Library/Digit/kurkov2019a284005.md` identified no exact prior proof in
their inspected scope. The OEIS text endpoint reading on 2026-10-28
independently confirms the quoted line and its "Conjecture" label.
Neither observation establishes global openness or priority.

The sequence definition and binary-weight lemmas already exist in the
repository. The sealed result addresses the complete 2019 question;
the imported sequence supplier's 2023 binomial theorem does not supply
this identity. Preregistration and outstanding delivery obligations
are associated with issue #23151; this dossier adds no mathematical claim.

## Route

The result reuses `KurkovWeightProductBinomial.a` and
`DyadicRowPolynomialRecurrence.wt`, together with the retained
binary-weight zero, even and odd lemmas. For arbitrary depth `L` and
`m<2^L`, prefix products satisfy `a(m)=P(L,1,m)` and
`a(2^L+m)=2*P(L,2,m)`. A zero-bit change increases the relevant prefix
weights by one. Induction on depth proves the product identity with
the sum over zero positions. The one positions supply
`wt(m)*P(L,1,m)`, restoring the complete sum. Exact logarithmic bounds
then identify `m=n-2^L` and preserve the source's literal n-based bit.

The proof is native repository mathematics. The source supplies the
question; no external proof is imported. The symbolic unbounded proof
has `utility: none`. The canonical result Scribe carries the typed
`OpenProblemResolutionClaim` for this dossier.

## Falsifier

An `n>1` where the stated whole sum differs from `a(n)` refutes the
identity. A discrepancy in either initial value, the defining recurrence,
the interpretation of the leading-bit deletion, or any omitted existing-one
summand invalidates the claimed correspondence with the source question.

## Evidence

The retained Lean declaration is
`D5/S1/Digit/KurkovLowerBitRecurrence.result`; its canonical exposition
is `Blueprint/D5/S1/Digit/KurkovLowerBitRecurrence.scribe.cs`.
The result's registration is retained in
`Reg/D5/S1/Digit/KurkovLowerBitRecurrence.lean`, alongside the three
helper registrations in the mirrored DyadicRowPolynomialRecurrence
module. Current compilation and canonical validation determine their
evidence status; this dossier is not a build receipt or proof authority.

Source quotations and the adapted statement are attributed to Mikhail
Kurkov, entry author Antti Karttunen, and OEIS contributors under
[CC-BY-SA-4.0](https://creativecommons.org/licenses/by-sa/4.0/).
The entry history is https://oeis.org/history?seq=A284005.

## Triage

`theorem`; exactly the full 2019 lower-bit identity, with the source's
initial values, recurrence and domain. Resolution membership is derived
from the typed Scribe claim and current frozen declaration.

## ASSUMED-UNVERIFIED

Global historical openness and priority remain unverified. OpenAlex
rate limiting, unavailable StackExchange advanced-search responses,
and unavailable GitHub code-search authorization limit the inherited
literature screen. This batch performs no new broad literature search.
OEIS's label alone does not establish worldwide openness. Independent
review, required CI and publication remain separate delivery obligations.
