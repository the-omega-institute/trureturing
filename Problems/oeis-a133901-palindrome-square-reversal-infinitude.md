---
slug: oeis-a133901-palindrome-square-reversal-infinitude
bibkey: brockhaus2007a133901
doi: null
url: https://oeis.org/A133901
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude
---

# Palindrome-square reversal infinitude in A133901

## Problem

OEIS A133901, NAME (verbatim):

> Numbers in A128921 whose square is not a palindrome.

OEIS A128921, NAME (verbatim):

> Palindromes m such that reverse of m^2 is also a square.

OEIS A133901, COMMENT (verbatim):

> Conjecture: Sequence is infinite.

Thus membership means a decimal palindrome `p` whose square is not a
palindrome and whose reversed square is a perfect square. In the formal
module, `rev10` is the numeric value of the reversed decimal string; it is
distinct from the digit-list reversal `D` in
`D5/S3/Arith/SumInConcatenation.lean`.

## Motivation

Brockhaus and Seidov recorded this unboundedness conjecture in 2007. Proving
the full statement produces an explicit member above every natural bound and
resolves the conjectured infinitude, rather than extending the finite table.

## Gap

The surfaces recorded in preregistration issue #7465 and checked by the probe
on 2026-09-13 were all three OEIS revisions, exact identifier searches on
arXiv, OpenAlex, MathOverflow, and GitHub, and the pinned Lean library search
surfaces. Revision #1 introduces the conjecture; revisions #2 and #3 only
change author formatting. The four exact identifier searches each returned
zero relevant proof or refutation hits. Fried's 2025 and 2026 JIS sequence
lists do not contain A133901 according to the GPT Pro search seat; that
reading is `ASSUMED-UNVERIFIED` at the level of the two papers' full text.
This is a bounded search report, not an exhaustive literature or priority
claim.

## Route

Given a bound `B`, put `j = B + 5`, `t = 10^j`, and

`P_j = 100t^4 + 110t^3 + 90t^2 + 11t + 1`,

`Q_j = 100t^4 + 110t^3 - 9t^2 + 11t + 1`.

The decimal representation of `P_j` is the `(4j+3)`-digit palindrome

`1 0^(j-1) 11 0^(j-1) 9 0^(j-1) 11 0^(j-1) 1`.

The private block-digit reconstruction lemma `digits_of_pow_blocks` gives
the decimal strings of `P_j`, `P_j^2`, and `Q_j^2`: `P_j` uses five blocks,
while each square uses nine five-digit blocks separated by `j-5` zeros.
Decimal reversal is therefore block-order reversal together with in-block
reversal. The resulting identity is `rev10(P_j^2) = Q_j^2`. Since
`P_j - Q_j = 99t^2 > 0`, it follows that
`rev10(P_j^2) = Q_j^2 < P_j^2`, so `P_j^2` is not a palindrome. Finally,
`P_j > B`, and the construction supplies a member above every bound.

## Falsifier

A natural bound `B` above which no A133901 member exists would contradict
the theorem. Equivalently, failure of palindrome membership, the reversed
square identity, or the strict square inequality for any constructed `P_j`
would invalidate the route.

## Evidence

- Lean module:
  `D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.lean`.
- Main theorem: `brockhaus_seidov_a133901`.
- The theorem's axiom report is std3: `propext`, `Classical.choice`, and
  `Quot.sound`.
- The orchestrator checked the family for `j = 5..12` and exhaustively
  searched `p < 10^6`, finding exactly `{33, 99}`.
- The probe independently repeated the same family range and exhaustive
  search, with the same results.

## Triage

`theorem`. The Lean theorem proves an A133901 member exists above every
natural bound, establishing the full conjectured infinitude.

## ASSUMED-UNVERIFIED

The absence of A133901 from the full texts of Fried's 2025 and 2026 JIS
papers was supplied by the GPT Pro search seat and was not independently
rechecked by this implementation seat. The literature search is bounded to
the dated surfaces in Gap. No exhaustive literature or first-publication
claim follows. Source-to-Lean identification is not itself kernel-checked.
