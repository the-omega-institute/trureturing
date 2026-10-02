---
slug: oeis-a395531-greedy-brick-all-index
bibkey: udovenko2026a395531
doi: null
url: https://oeis.org/A395531/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/GreedyBrick/OriginalIdentity
---

# The greedy-brick all-index identity

## Problem

OEIS A395531, revision 30, Aleksei Udovenko:

> Conjecture: when n = a(m) for some m, we have a(n) = n(n+3)/2 - m. Verified experimentally up to m=1172, n=688491.

Rows are numbered from one. The value a(m) is the width of the first brick
in row m under the literal highest-supported-row placement rule. The exact
assertion is a(a(m)) = a(m)(a(m)+3)/2-m for every integer m >= 1.

## Motivation

This first-tier externally named conjecture asks for an identity at every
positive index. Totality and correspondence to actual row births are part
of its meaning.

## Gap

The source entry still labels the assertion a conjecture. The bounded
literature scope recorded in issue 11600 covers all thirty entry revisions,
the linked optimized generator, related entries, jOEIS and OEIS-Python,
identifier searches on arXiv and Crossref, and bounded GitHub Lean searches.
No published resolution was found in that scope. The frozen predecessor,
band and trace declarations do not state the original all-index identity;
the pinned Mathlib search supplied no matching theorem.

## Route

The literal capacity trajectory has a least birth for every positive row.
An initialized cofinal rest trace samples that same trajectory. The local
block-prefix induction proves that height stays constant strictly before
the final brick of each rest block. Thus the least literal birth of row m
is precisely the endpoint of the event birth of m.

Write b(m) for that endpoint. The frozen successor band gives the exact cut:
a renewal f lies before birth b(m) if and only if its predecessor lies before
birth m. The frozen successor inverse laws turn this into a weight-preserving
bijection. Endpoint increments telescope to bin weights. Births through
height b(m) contribute b(m)(b(m)+1)/2; renewals contribute b(m)-m. Their
sum is b(m)(b(m)+3)/2-m, and the birth correspondence gives the original
literal-sequence identity.

## Falsifier

A positive m for which both actual births exist and the displayed identity
fails would refute the assertion. No matching finite prefix is used as proof.
The chronological-word-copy counterexample at brick 242 rejects a stronger
route, while the raw EventLaws countermodel lacks the actual rest-trace
hypotheses; neither is a counterexample to this assertion.

## Evidence

The mathematical source is D5/S3/Combinatorics/GreedyBrick/OriginalIdentity.lean.
Its sole theorem result quantifies over every m >= 1 and assumes no trace,
recurrence, cut law or new birth premise. Its axiom closure is propext,
Classical.choice and Quot.sound. The definition a uses the already proved
least literal birth at positive indices; its unused zero value is zero.

## Triage

Proved in the local proof of
`D5/S3/Combinatorics/GreedyBrick/OriginalIdentity.result`: the strict-prefix
property of first-zero blocks connects event births to physical births, and
the predecessor bijection preserves renewal weights without requiring
chronological order of renewal labels. The event identity is also proved
there for every initialized unbounded `RestTrace`.

Open: extensions to other placement rules require their own literal birth
correspondence.

Source evidence: no dependent theorem or follow-up question relying on the
conjecture was identified in the inspected original OEIS entry.

## ASSUMED-UNVERIFIED

The bounded source search does not establish first-publication priority.
The source-to-Lean interpretation uses the frozen row-scan and common
labelled-history correspondence. The linked optimized generator's license
has not been verified, and its source is not redistributed.
