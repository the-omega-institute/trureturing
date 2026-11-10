---
bibkey: howroyd2026a391632
authors: Andrew Howroyd; Eric W. Weisstein
year: 2026
title: "OEIS A391632: mutual-visibility subsets of Andrasfai graphs"
doi: null
url: https://oeis.org/A391632/internal
claim: "Conjectured g.f.: x*(4 - 19*x + 33*x^2 - 40*x^3 + 8*x^4)/(1 - 10*x + 29*x^2 - 32*x^3 + 8*x^4)."
strata_touched:
  - D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual
license: citation-only
triage: anchor
---

# Howroyd's Andrasfai subset-count identity

OEIS A391632, revision 27, attributes the displayed generating-function
conjecture to Andrew Howroyd, January 12, 2026. The sequence is attributed
to Eric W. Weisstein and has offset 1,1. Its name is "Number of
mutual-visibility sets in the n-Andrásfai graph."

The original n-Andrasfai graph is the Cayley graph on the labelled vertices
of $\mathbb Z/(3n-1)\mathbb Z$ with connection set
$\{1,4,\ldots,3n-2\}$, for every $n\ge1$. A mutual-visibility subset permits,
for each distinct selected pair, a shortest path in the original host
whose internal vertices avoid the selected subset. All labelled subsets
are counted, including the empty set and singletons.

The source's index-one count is four. The trace representation of the
four-state automaton has index-one trace three, so the actual generating
series has the explicit first-degree correction $+X$.

## Verified locator

- Exact conjecture, `%F`, offset `%O`, and sequence name `%N`:
  https://oeis.org/A391632/internal (revision 27).
- Original graph convention:
  https://mathworld.wolfram.com/AndrasfaiGraph.html.
- Mutual-visibility definition and subset-count polynomial:
  Bujtas, Klavzar and Tian, arXiv:2412.03066v1, Introduction and Definition 3.1,
  https://arxiv.org/html/2412.03066v1.

The OEIS conjecture is the external statement source, rather than a proof
of the counting correspondence. Programs generated from the conjectured
series and finite coefficient agreement do not establish that
correspondence. This note redistributes no source program.
