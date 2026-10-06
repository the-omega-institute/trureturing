---
bibkey: erdoslovasz1975polychromatic
authors: Paul Erdos; Laszlo Lovasz
year: 1975
title: "Problems and results on 3-chromatic hypergraphs and some related questions"
doi: null
url: https://users.renyi.hu/~p_erdos/1975-34.pdf
claim: "Independent random vertex colors and the local lemma give a coloring containing every color on every sufficiently large edge with bounded intersection degree."
strata_touched:
  - D5/S3/Combinatorics/Probability/UniformPolychromatic
license: citation-only
triage: anchor
---

# Polychromatic hypergraph coloring

Theorem 3, printed page 611, gives a sufficient intersection-degree bound for
an r-uniform hypergraph to have a k-coloring containing every color on every
edge. The proof on printed page 618 colors vertices independently and uniformly,
uses the event that an edge misses at least one color, and bounds its probability
by `k (1 - 1/k)^r`. The dependency graph is the intersection graph of the indexed
hyperedges. The argument does not require a linear hypergraph or intersections
of size at most one.

## Verified locator

https://users.renyi.hu/~p_erdos/1975-34.pdf

Paul Erdos and Laszlo Lovasz, *Problems and results on 3-chromatic hypergraphs
and some related questions*, Infinite and Finite Sets, Colloquia Mathematica
Societatis Janos Bolyai 10 (1975), 609-627. Theorem 3 is on page 611; its proof
is on page 618. The PDF is used as a mathematical reference, not redistributed
as part of the formal proof source.

## Exact reused argument

Each missing-color event depends only on its edge's vertex coordinates. Any
joint intersection of events from nonintersecting edges depends only on
complementary coordinates, which supplies the full independence requirement.
The original proof uses the paper's Lemma 2. The formal application uses the
finite symmetric local lemma with criterion `exp(1) p (D+1) ≤ 1`, supplied by
the separately attributed ATLAS proof. It also allows unequal edge sizes,
using a common lower bound s, so its sufficient criterion is
`exp(1) L ((L-1)/L)^s (D+1) ≤ 1`.

This is an application of the classical probabilistic method. It gives a single
coloring for the whole finite indexed family, not separate favorable colorings
for individual edges, and does not assert an efficient coloring algorithm.
