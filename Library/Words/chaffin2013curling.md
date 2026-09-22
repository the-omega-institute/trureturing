---
bibkey: chaffin2013curling
authors: Benjamin Chaffin, John P. Linderman, N. J. A. Sloane, Allan R. Wilks
year: 2013
title: "On curling numbers of integer sequences"
doi: 10.48550/arXiv.1212.6102
url: https://arxiv.org/abs/1212.6102v3
claim: "The last sentence of Section 5 asks whether Theorem 23 survives when the starting sequence may contain a 1 but does not end with 1; Section 6 lists it as open question 12."
strata_touched:
  - D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation
license: citation-only
triage: anchor
---

# Chaffin--Linderman--Sloane--Wilks curling numbers

## Verified locator

DOI: 10.48550/arXiv.1212.6102

URL: https://arxiv.org/abs/1212.6102v3

Version: arXiv:1212.6102v3, the text that matches the journal article
*Journal of Integer Sequences* **16** (2013), Article 13.4.3. Version 2 of the
arXiv record numbers the conjectures differently and states a smaller verified
range, so the version is load bearing. The authors and title match both the
arXiv record and the journal record.

## Definitions

Section 1 defines the curling number `cn(S)` of a finite integer sequence as
the largest `k` such that `S = X Y^k` for some nonempty `Y`. For a starting
sequence `S_0` it sets `S_{m+1} = S_m cn(S_m)`. When `cn(S_t) = 1` holds for
some `t >= 0`, the least such `t` is the tail length `tau(S_0)` and
`S^(e) := S_t` is the extension of `S_0`. Section 5 writes `G` for Gijswijt's
sequence A090822, the continuation of the one-element sequence `1`, and
`S^(inf)` for the infinite continuation of `S`.

## The statement in question

Section 5 states:

> Theorem 23. Assume the curling number conjecture is true. Let S be an initial
> sequence not containing a 1, let S^(e) be its "extension" (defined in §1), and
> let S^(inf) be its infinite continuation. Then S^(inf) = S^(e) G.

The section closes with:

> We do not know if the theorem is still true if S is allowed to contain a 1 but
> does not end with 1.

Section 6, which collects the article's open questions, lists as item 12:

> 12. The question implicit in the last sentence of §5.

The prose immediately before Theorem 23 phrases the informal content as "any
starting sequence S that does not contain a 1 must eventually merge with G".
That phrasing is weaker than the displayed equality; the question in item 12
refers to "the theorem", whose conclusion is the displayed equality.

## Where the published proof breaks

The proof of Theorem 23 writes `S^(inf) = W(XT)^n n ⋯` with `S^(e) = WX` and `T`
a prefix of `G`, and in the case `n = 2` argues that the curling number of the
first copy of `T` is the first term of `X`, "which is not 1". That step uses the
hypothesis that `S^(e)` contains no 1. Weakening the hypothesis to "contains a 1
but does not end with 1" keeps `S^(e)` from ending in 1 but does not keep `X`
from beginning with 1.

## Scope of the recorded answer

The starting sequence `1 2` contains a 1 and does not end with 1. Since
`cn(1 2) = 1`, its tail length is 0 and its extension is `1 2` itself, so the
extension exists without appeal to the curling number conjecture. Its
continuation begins `1 2 1 1 2 1 2 2 2 3`, whereas `S^(e) G` begins
`1 2 1 1 2 1 1 2 2 2`; the two differ at the seventh term because
`1 2 1 1 2 1 = (1 2 1)^2` has curling number 2.

Because Theorem 23 is stated under the hypothesis that the curling number
conjecture holds, the weakened statement read as an implication can still be
true vacuously. The recorded result negates its consequent, so the weakened
implication is equivalent to the negation of the curling number conjecture: a
proof of the weakened Theorem 23 would refute that conjecture.

The weaker informal reading, whether `S^(inf)` has a suffix equal to a suffix of
`G`, is a different statement and is not settled here. Sloane's 2023
retrospective conjectures that merging holds for any starting sequence.

## Bounded prior-resolution evidence

Issue 9218 records the screen carried out before the result was written up. An
independent literature pass opened the journal article, the two-author
Chaffin--Sloane preprint arXiv:0912.2382v5, Sloane's 2023 retrospective, both
arXiv versions and the journal version of Levi van de Pol's growth-rate work,
the OEIS entries A090822, A093369, A094004, A216955 and A217209 with the OEIS
curling-number index, and several citing papers including Caveney, Dong and
Shallit, arXiv:2608.15670v1. None of them records an answer to item 12. Major
citation-index result pages were not reachable, so this is a bounded negative
finding and no worldwide priority claim is made.
