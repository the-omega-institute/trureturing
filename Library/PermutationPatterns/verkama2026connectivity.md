---
bibkey: verkama2026connectivity
authors: Emil Verkama
year: 2026
title: "Permutation patterns and higher connectivity in inversion graphs"
doi: 10.48550/arXiv.2611.17237
url: https://arxiv.org/html/2611.17237v1
claim: "Conjecture 6.2 asks for inv(pi) >= (7/4)|pi| - 3 for every 351624-avoiding permutation with a vertex-2-connected inversion graph."
strata_touched:
  - D5/S3/Combinatorics/Permutation/Verkama62Local
  - D5/S3/Combinatorics/Permutation/Verkama62Persistence
  - D5/S3/Combinatorics/Permutation/Verkama62Count
  - D5/S3/Combinatorics/Permutation/Verkama62Charge
  - D5/S3/Combinatorics/Permutation/Verkama62Representation
  - D5/S3/Combinatorics/Permutation/Verkama62Graph
  - D5/S3/Combinatorics/Permutation/Verkama62EarGeometry
  - D5/S3/Combinatorics/Permutation/Verkama62Run
  - D5/S3/Combinatorics/Permutation/Verkama62Result
license: citation-only
triage: anchor
---

# Permutation patterns and inversion-graph connectivity

The graph has the permutation's values as vertices. Values u and v are adjacent when
(u-v)(pi inverse(u)-pi inverse(v)) is negative. Thus each inversion contributes one
unordered edge. Ordinary vertex-2-connectivity requires at least three vertices,
connectedness, and connectedness after deletion of any one vertex.

Conjecture 6.2 states that every classically 351624-avoiding permutation whose inversion
graph is vertex-2-connected satisfies inv(pi) >= (7/4)|pi| - 3. This has no additional
321-avoidance, bipartiteness, finite-size or asymptotic hypothesis. Equivalently,
7|pi| <= 4 inv(pi) + 12.

Lemma 2.6 constructs induced ear decompositions of finite vertex-2-connected graphs.
Corollary 2.9 bounds ear sizes in chordal classes. Lemma 3.3 gives an initial induced
triangle or square containing the original leftmost and bottommost permutation points.
Lemma 3.6 identifies the order geometry of an induced two-vertex ear. In an anchored
decomposition, the new maximum is inserted immediately before the old rightmost point,
and the new rightmost value is immediately below the old maximum.

The local terminal-3412 obstruction and the integer-potential argument connect this
geometry to the coefficient seven quarters. A fresh terminal 3412 survives zero or one
singleton of old degree two. A subsequent northeast double ear then gives a classical
351624 occurrence. The signed potential is 7|V|-4|E|. The complete run theorem constructs such a run from ordinary vertex connectivity,
using the two original extreme points as anchors. This avoids assuming a source-ear
lemma and supplies the full rational bound under the hypotheses of Conjecture 6.2.

## Source locators

- Conjecture 6.2: `S6.Thmtheorem2`.
- Lemma 2.6: `S2.Thmtheorem6`.
- Corollary 2.9: `S2.Thmtheorem9`.
- Lemma 3.3: `S3.Thmtheorem3`.
- Lemma 3.6: `S3.Thmtheorem6`.

The cited version is arXiv:2611.17237v1. The source HTML has SHA-256
`b66f3c0145983d265aeadc973a1062b6f7e03a20e7805a87e096750f74d5e833`.
This citation does not certify worldwide openness or priority.

## Verified locator

- DOI: 10.48550/arXiv.2611.17237
- Version: https://arxiv.org/html/2611.17237v1
