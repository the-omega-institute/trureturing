---
bibkey: testart2026minimal
authors: Benjamin Testart
year: 2026
title: "On minimal pattern-containing inversion sequences"
doi: null
url: https://arxiv.org/abs/2602.12130v2
claim: "Section 7 Question 1 asks for bijections from the Section 6 families IP or T to known type-C poly-Bernoulli models."
strata_touched:
  - D5/S3/Combinatorics/PriorityLattice/TestartTreeCode
  - D5/S3/Combinatorics/PriorityLattice/TestartTraversal
license: citation-only
triage: anchor
---

## Source contract

Source: https://arxiv.org/html/2602.12130v2 ; Section 6, the definition
of the rooted increasing trees T, and Section 7, Question 1, printed page 17.
The article title and Question 1 are readable in the public arXiv HTML.
The corresponding thesis is *Pattern avoidance in inversion sequences*,
Chapter 4, Sections 4.6–4.7, printed pages 125–127:
https://theses.hal.science/tel-05787447v1/document .

Question 1 asks:

> Find bijections between the families IP or T of Section 6 and other
> families of combinatorial objects known to be counted by the
> poly-Bernoulli numbers of type C.

The displayed source indices are IP(n,k) and T(n,k). Here T(a,b) has
labels 0 through a+b-1, root 0, internal labels exactly 0 through a-1,
and leaves exactly a through a+b-1. Trees are unordered and increasing.
The positive labels are encoded by Fin(a+b-1), with one added to each
index; the existing native carrier stores root and all parent incidences.

The construction deletes root 0 and reads each
component in preorder with decreasing child-root order. It turns these
words into cycles in their given direction, then applies D. Its inverse
applies D, starts every cycle at its minimum, attaches each later entry
to its rightmost preceding smaller entry, and restores root 0.

The whole fixed-map theorem is the target in issue 22578:
https://github.com/the-omega-institute/trureturing/issues/22578#issuecomment-6431545799 .
An insertion equivalence or equality of counts alone does not verify the
fixed traversal and reconstruction. No resolution or priority claim is
made by this source note. Literature searches have not established prior
coverage of the exact individual-label tree contract; this is a bounded
applicability result, not novelty clearance.

This note contains bibliographic attribution and a short question quotation;
it does not redistribute article or thesis source. `citation-only` describes
this repository's use and grants no license over the original works.

## Verified locator

https://arxiv.org/abs/2602.12130v2
