---
slug: chaffin-sloane-gijswijt-merge-refutation
bibkey: chaffin2013curling
doi: 10.48550/arXiv.1212.6102
url: https://arxiv.org/abs/1212.6102v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.result
---

# Chaffin-Linderman-Sloane-Wilks Gijswijt Merge Refutation

## Problem

Chaffin, Linderman, Sloane and Wilks, *Journal of Integer Sequences* 16 (2013),
Article 13.4.3 = arXiv:1212.6102v3, Section 5, Theorem 23, state: "Assume the
curling number conjecture is true. Let S be an initial sequence not containing a
1, let S^(e) be its 'extension' (defined in §1), and let S^(inf) be its infinite
continuation. Then S^(inf) = S^(e) G." Here `G` is Gijswijt's sequence A090822,
`cn(S)` is the largest `k` with `S = X Y^k` for nonempty `Y`, the continuation
appends `cn` repeatedly, and the extension is the first prefix whose curling
number equals one.

The section closes: "We do not know if the theorem is still true if S is allowed
to contain a 1 but does not end with 1." Section 6 lists this as open question
12: "The question implicit in the last sentence of §5."

## Motivation

The frozen theorem
`D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.result` settles
that question in the negative. The consequent of the weakened statement is false
outright, so the weakened Theorem 23, read as an implication whose hypothesis is
the curling number conjecture, is equivalent to the negation of that conjecture:
a proof of the weakened theorem would refute it.

## Gap

Issue 9218 records the screen carried out before write-up. An independent
literature pass opened the journal article, the Chaffin-Sloane preprint
arXiv:0912.2382v5, Sloane's retrospective arXiv:2301.03149v2, both arXiv
versions and the journal version of Levi van de Pol's growth-rate work, the OEIS
entries A090822, A093369, A094004, A216955 and A217209 with the OEIS
curling-number index, and citing papers including Caveney, Dong and Shallit,
arXiv:2608.15670v1. None records an answer to item 12. Major citation-index
result pages were not reachable, so this is a bounded negative finding.

## Route

Take `S = 1 2`. It contains a 1 and does not end with 1. Since `cn(1 2) = 1` the
tail length is zero and the extension is `1 2` itself, so the extension exists
without appeal to the curling number conjecture. The continuation is computed
term by term: `cn(1 2) = 1`, `cn(1 2 1) = 1`, `cn(1 2 1 1) = 2`,
`cn(1 2 1 1 2) = 1`, `cn(1 2 1 1 2 1) = 2` because `1 2 1 1 2 1 = (1 2 1)^2`.
So the continuation begins `1 2 1 1 2 1 2 2 2 3`, while `S^(e) G` begins
`1 2 1 1 2 1 1 2 2 2`. They differ at the seventh term.

The published proof breaks at exactly that point. It writes
`S^(inf) = W(XT)^n n ⋯` with `S^(e) = WX` and `T` a prefix of `G`, and for
`n = 2` argues that the curling number of the first copy of `T` is the first term
of `X`, "which is not 1". Here `W` is empty, `X = 1 2`, `T = 1` and `n = 2`, and
the first term of `X` is 1.

## Falsifier

A different value for `cn(1 2 1 1 2 1)`, a different tail length for `1 2`, or a
different eighth term of Gijswijt's sequence would invalidate the witness. The
first eleven terms of `G` are `1 1 2 1 1 2 2 2 3 1 1`; its first 4 occurs at term
220, which the source states independently.

## Evidence

The weaker reading, whether the continuation of a starting sequence containing a
1 has a suffix equal to a suffix of `G`, is a different statement and is not
settled here. Sloane states that weaker form as a conjecture for every starting
sequence in arXiv:2301.03149v2, Section 4.3: "If true, this implies that if the
starting sequence contains no 1s, then the sequence eventually becomes
Gijswijt's sequence [5, Th. 23]. In fact I conjecture that this is true for any
starting sequence."

Measured evidence bearing on the weaker form, for the same starting sequence
`1 2`: computing 24000 terms of both the continuation and `G`, every pair of
offsets below 6000 gives an aligned common run that ends in a disagreement
inside the computed range; the longest such run is 1740 terms, beginning at
index 3619 of the continuation and index 30 of `G`. Runs of this kind lengthen
with the computed range, which is consistent with agreement on longer and longer
stretches without a shared tail. No suffix equality is thereby excluded beyond
the searched offsets and range, so the weaker question stays open.

Whether the starting sequences containing a 1 that do satisfy the displayed
equality admit a characterization is also open. Among the 57002 sequences over
`{1,2,3}` of length at most ten that contain a 1 and do not end in 1, 18369
disagree with `S^(e) G` within 120 appended terms; the remaining 38633 agree
over that range, which leaves the infinite equality undecided for them.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9218
before write-up. The admission basis is `open-problem-resolution`; the
conservative classification is `proof_shape: bind-only` with
`escape_witness: none`. The computational use is a `certified-instance` with a
typed `refutes` edge from `result` to `claim`.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the journal article, the Chaffin-Sloane
preprint arXiv:0912.2382v5, Sloane's retrospective arXiv:2301.03149v2, both
arXiv versions and the journal version of van de Pol's growth-rate work, the
OEIS entries A090822, A093369, A094004, A216955 and A217209 with the OEIS
curling-number index, and citing papers including arXiv:2608.15670v1 were
opened; citation-index result pages were not reachable, so no worldwide
priority claim is made.

Among the 57002 sequences over `{1,2,3}` of length at most ten that contain a 1
and do not end in 1, the 38633 that agree with `S^(e) G` over 120 appended terms
are surviving candidates only; finite agreement does not establish the infinite
equality for them.

The weaker reading, whether the continuation has a suffix equal to a suffix of
`G`, is not settled here. For `S = 1 2`, computing 24000 terms of both sequences
gives an aligned common run that ends in a disagreement at every pair of offsets
below 6000, the longest being 1740 terms; that excludes a shared tail only
within the searched offsets and range.
