---
bibkey: kimberling2017a288476
authors: Clark Kimberling
year: 2017
title: "OEIS A288476: lengths of nonoverlapping replacement iterates"
doi: null
url: https://oeis.org/A288476
claim: "Conjecture: a(n) is the number of letters (0's and 1's) in the n-th iteration of the mapping 00->0101, 1->011, starting with 00; see A288473."
strata_touched:
  - D5/S1/Words/KimberlingA288476Length
license: citation-only
triage: anchor
---

# Kimberling's replacement-iterate lengths

## Locator

Declared entry: <https://oeis.org/A288476>.

The exact source is [OEIS A288476](https://oeis.org/A288476/internal),
COMMENTS and FORMULA, revision 8. Its defining recurrence is
`a(n)=a(n-1)+4*a(n-2)-2*a(n-3)`, with initial values `2,4,8` at
indices `0,1,2`. The length conjecture first appears in revision 2,
as visible in the [public change history](https://oeis.org/history?seq=A288476).
The original revision was checked through that history by the independent
source probe, rather than an authenticated individual-revision snapshot.
The current entry retains the word Conjecture.

The linked [A288473 program](https://oeis.org/A288473/internal), revision 9,
starts with `s={0,0}` and applies
`StringReplace[w[n-1], {"00" -> "0101", "1" -> "011"}]`.
[Wolfram's StringReplace documentation](https://reference.wolfram.com/language/ref/StringReplace.html)
specifies scanning successive positions and resuming after the end of a
matched substring. Thus each pass consumes nonoverlapping original-input
matches and retains unmatched zeros; emitted output is not rescanned.
[A288551](https://oeis.org/A288551/internal), revision 9, repeats the same
length conjecture. These three length statements are one event. The names
of the odd and even limiting words do not restrict the iterate index.

The quotations are attributed to Clark Kimberling and OEIS; the OEIS text
is available under CC-BY-SA-4.0. This note retains citations and short
source quotations, not a copy of the sequence database. The scanner proof
and exposition are repository derivations. The reused Mathlib recurrence
and semiconjugacy results are under Apache-2.0.

The nearby Dvorakova–Pelantova–Shallit paper,
*On a sequence of Kimberling and its relationship to the Tribonacci word*,
[arXiv:2510.11318v5](https://arxiv.org/html/2510.11318v5), concerns
`1->10`, lengths `2,4,6,10`, and an order-four relation. Its finite-block
recoding method is prior art; its statements do not settle this `1->011`
length conjecture. The pinned jOEIS A288476 implementation at
`29b1fc0a46b2722340a61eac75b3ccb31cbde3b7` only generates the recurrence.
The independent probe's exact-ID arXiv and Crossref queries found no
settlement in their bounded scope. Worldwide priority remains
ASSUMED-UNVERIFIED.
