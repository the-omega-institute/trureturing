---
bibkey: banaschewski1955nulldimensional
authors: Bernhard Banaschewski
year: 1955
title: Über nulldimensionale Räume
doi: 10.1002/mana.19550130302
url: https://doi.org/10.1002/mana.19550130302
claim: The zero-dimensional compactification underlying the boundary-avoiding Boolean graph construction is classically attributed to Stone and Banaschewski.
strata_touched:
  - D5/S3/Topology/Resolution
  - D5/S1/Dynamics/StableRange
license: citation-only
triage: anchor
---

# Classical attribution and exact formalized scope

## Verified locator

DOI: 10.1002/mana.19550130302. Canonical URL:
https://doi.org/10.1002/mana.19550130302. Crossref verifies the bibliographic
metadata only; the original article has not been inspected.

## Construction and scope

Banaschewski's article appears in Mathematische Nachrichten 13, 129–140.
The title, author, bibliographic coordinates and DOI are verified against
Crossref. The original article has not been inspected, so no theorem number
or claim about its exact relative formulation is attributed to it.

For compact Hausdorff X and closed zero-dimensional C, consider all actual
subsets A of X whose ambient frontiers miss C. Their characteristic functions
are locally constant near each point of C. They are the clopen subsets of
the Michael modification obtained by isolating X outside C while retaining
the original neighborhoods at C. The classical Stone/Banaschewski picture
motivates compactification by all these Boolean coordinates.

RelativeBoolean formalizes the closure of the actual membership graph in
X times the binary cube. It directly proves the separating-neighborhood
lemma, injection of the cube projection, zero-dimensionality, singleton
fibers over C, and a continuous section homeomorphic to the full inverse
image of C. Continuous maps of pairs act by actual inverse images of
admissible subsets, giving continuous coherent lifts. Identification with
a universal compactification is explanatory context, not an additional
formalized universal-property theorem.

The relative graph arguments and the stable-range identity are presented
as repository derivations using pinned Mathlib separation and compactness
results. The compactification itself is classical. There is no mathematical
priority claim. No metric, countability, nonemptiness, openness or onto
condition on pair maps is imposed. The stable-range identity uses all
natural iterates including zero and needs only continuity on a topological
space. Compact Hausdorff hypotheses separately give a compact stable core
with an onto continuous restriction.

These results do not assert shadowing for the resolution. They do not supply
finite observation names, a core period or a general shadowing extension.
Peng's unrestricted Question 5.1 remains outside the construction.
