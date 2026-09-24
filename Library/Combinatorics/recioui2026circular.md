---
bibkey: recioui2026circular
authors: Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai
year: 2026
title: "Circular s-choice parking functions: an exact closed formula via rotational symmetry"
doi: 10.48550/arXiv.2609.23607
url: https://arxiv.org/html/2609.23607v1
claim: "Open Problem 1 asks for a canonical bijection between every fixed-increment, fixed-vacancy anchor class in the circular two-choice d=1 model and the classical parking functions."
strata_touched:
  - D5/S3/Combinatorics/CircularTwoChoiceParkingOperational
  - D5/S3/Combinatorics/CircularTwoChoiceParkingBijection
license: CC0-1.0
triage: anchor
---

# Circular s-choice parking functions

## Verified locator

DOI: 10.48550/arXiv.2609.23607
URL: https://arxiv.org/html/2609.23607v1

The canonical source is arXiv:2609.23607v1, submitted on 2026-09-20. The
arXiv API returned exactly that version on 2026-09-25, and the current HTML
still labels the bijection request as Open Problem 1. The title, author names,
abstract, five numbered sections, and reference list were checked against the
full HTML source. The title page orders the authors as Asma Recioui, Hacène
Belbachir, and Abdelhakim Ait-Zai; the arXiv API lists the same three names but
places Hacène Belbachir first. The title-page order is retained here. The HTML
record declares CC Zero.

## Model and established results

There are `n` cars and `m=n+1` circular spots. An admissible `s`-tuple starts
at an anchor and advances clockwise by `s-1` positive increments, with every
successive gap and the return gap at least `d`. A car tries the tuple entries
in order and, if all are occupied, continues clockwise from its last choice.
Every circular input parks all cars and leaves one spot empty.

The paper proves by rotation that the vacancy is equidistributed. It then
refines the argument at a fixed increment matrix: rotating every anchor
preserves the increments and moves the vacancy transitively, so every vacancy
fiber has size `m^(n-1)`. For `s=2` and `d=1`, the total conditioned count is
`(n+1)^(n-1) n^n`. The factor `(n+1)^(n-1)` is the classical parking-function
count and `n^n` counts the independent per-car increments. These counts,
equidistribution, the factorization, Pollak's rotation argument, and the
Kaplansky circular-selection count are results or acknowledged background of
the source; they are not new credit for the repository construction.

## Exact open problem

Open Problem 1 reads:

> Give a bijective proof of the factorization of Corollary 1 for d=1,
> refining Theorem 2 to a canonical bijection between each anchor class
> {E=j} intersect C_kappa and the set of classical parking functions.

In the two-choice specialization, each car has a literal ordered pair: the
anchor is tried first, and the second choice is the starting point of the
clockwise fallback scan. Fixing `kappa` fixes the positive clockwise increment
from the anchor to the second choice for every car. Thus the requested class
fixes all per-car increments and the final empty spot, while its free data are
the anchors. The question asks for an actual two-sided construction, not the
already proved equality of finite cardinalities.

## Repository correspondence

`CircularTwoChoiceParkingOperational` models the `s=2`, `d=1` rule on
`ZMod(n+1)`. Its scanner includes offset zero, so a free second choice is used
before any later clockwise spot. It proves prefix freshness, unique vacancy,
rotation equivariance, positive-increment encoding and decoding, and an
explicit equivalence between the literal fixed-increment fiber and a
one-choice circular fiber. It also defines cut and uncut coordinates around a
vacancy and proves the forward scanner simulation.

`CircularTwoChoiceParkingBijection` completes the reverse feedback-state
simulation against the frozen classical supplier. The public
`fixedFiberEquiv` is the exact fixed-increment, fixed-vacancy construction.
Its inverse rebuilds both entries of every ordered pair. The separate
`globalParkingEquiv` exposes the classical parking function, original
increment matrix, and actual vacancy together; its inverse uses the matching
fixed fiber and hence recovers every anchor and second choice. This global
product is an auxiliary interface, not a second formulation of Open Problem 1.

The formal definitions extend to `n=0`; the source problem and its claimed
resolution use only `n>=1`. At `n=1`, the only increment is one and the
offset-zero rule still distinguishes anchor priority from second-choice
priority. No quantifier over positive `n`, increment matrices, vacancy spots,
or cars is replaced by a finite sample.

## Bounded prior-art check

Two exact arXiv searches were performed on 2026-09-25: `circular parking` with
`bijection`, and `fixed increments` with `parking functions`. Both returned
zero records. The first twenty Crossref title results for `circular s-choice
parking functions` contained general parking-function papers and unrelated
parking-choice work, but no exact fixed-increment circular construction. An
OpenAlex query returned HTTP 429 and was unread.

This is only a not-found result in the stated search scope. It does not show
worldwide absence, priority, or absence from unpublished, unindexed,
paywalled, or author-held material. The current paper itself is the authority
for the open wording; later literature was not exhaustively read.
